-- lean/improves_bin/AbsSatBin/GraphMap/CnfMapBin.lean
import AbsSatBin.Cnf.Formula
import AbsSatBin.Utils.Alias

/-!
# The bin map of a CNF, as arithmetic

The pure mirror of `julia/improves_bin/src/graph_map/graph_map_bin.jl`, in the
style of `lean_project`'s `CnfMap`: no data structure, only the step arithmetic,
the nodes of each step, the requirement function, the sons, and the prohibited
windows. `MapBinDiff` checks every one of them against the map Julia builds.

## The encoding it reproduces (0-based variables `v`, clauses `j`)

| step | nodes |
|---|---|
| `0` | one `"FusionNode"` (root) |
| `2v+1` | `⟨2v+1,0⟩` (`"v=0"`), `⟨2v+1,1⟩` (`"v=1"`) — no requirements |
| `2v+2` | `⟨2v+2,i⟩` (`"!v=i"`), requiring `⟨2v+1, 1-i⟩` |
| `2n+1` | one `"FusionNode"` (middle) |
| `2n+2+3j+p` | `⟨·,b⟩`, `b ∈ {0,1}`: literal `p` of clause `j` has value `b`; requires `⟨lₚ.binStep, b⟩` |
| `2n+3m+2` | one `"FusionNode"` (top) |

so `stepCount = 2n + 3m + 3`. Every step has one or two nodes.

**The clause is no longer in the nodes.** In the classic map a clause step has
seven nodes and the omitted row `000` *is* the disjunction. Here every clause
step has both values, and the disjunction lives in the **prohibited window**:
the path node `(L1=0, L2=0, L3=0)` at the third step of each clause. It is a
fact about path identifiers (`PathNodeId`, window of three), not about map
nodes, so it is a separate predicate, `isProhibited`, which the UP consults.

**Requirements are one per node.** `reqOf` never returns more than one node, so
the classic `Functional` obligation is free (`reqOf_length_le_one`), and no
distinct-steps hypothesis is needed anywhere: only `Bounded`.

**Where the Julia map differs, knowingly.** With no clauses, Julia never leaves
the `"vars"` stage, so it builds neither the middle nor the top fusion node.
This module always builds them. The differential skips `m = 0`.
-/

namespace AbsSatBin.GraphMap.CnfMapBin

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf

-- ============================================================
-- The step arithmetic
-- ============================================================

def varStep (v : Nat) : Int := 2 * (v : Int) + 1
def negStep (v : Nat) : Int := 2 * (v : Int) + 2

def midFusion (φ : Cnf) : Int := 2 * (φ.nVars : Int) + 1
/-- The step of literal position `p` (`0`, `1`, `2`) of clause `j`. -/
def clauseStep (φ : Cnf) (j p : Nat) : Int :=
  2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + (p : Int)
def fusionTop (φ : Cnf) : Int := 2 * (φ.nVars : Int) + 3 * (φ.clauses.length : Int) + 2
def stepCount (φ : Cnf) : Int := 2 * (φ.nVars : Int) + 3 * (φ.clauses.length : Int) + 3

theorem varStep_eq (l : Lit) (h : l.pos = true) : l.binStep = varStep l.v := by
  simp [Lit.binStep, varStep, h]

theorem negStep_eq (l : Lit) (h : l.pos = false) : l.binStep = negStep l.v := by
  simp [Lit.binStep, negStep, h]; omega

/-- A literal of the formula sits strictly between the root and the middle fusion. -/
theorem lit_step_bounds (φ : Cnf) (l : Lit) (h : l.v < φ.nVars) :
    0 < l.binStep ∧ l.binStep < midFusion φ := by
  refine ⟨?_, ?_⟩ <;> (simp only [Lit.binStep, midFusion]; split <;> omega)

-- ============================================================
-- Clause steps
-- ============================================================

/-- Literal `p` of a clause: `0 ↦ l1`, `1 ↦ l2`, anything else `↦ l3`. -/
def litAt (c : Clause) : Nat → Lit
  | 0 => c.l1
  | 1 => c.l2
  | _ => c.l3

/-- The clause and literal position a clause step stands for. -/
def clauseOf (φ : Cnf) (k : Int) : Option (Clause × Nat) :=
  let o := k - midFusion φ - 1
  match φ.clauses[(o / 3).toNat]? with
  | none => none
  | some c => some (c, (o % 3).toNat)

theorem clauseOf_clauseStep (φ : Cnf) (j p : Nat) (c : Clause) (hp : p < 3)
    (hj : φ.clauses[j]? = some c) : clauseOf φ (clauseStep φ j p) = some (c, p) := by
  have hq : ((clauseStep φ j p - midFusion φ - 1) / 3).toNat = j := by
    simp only [clauseStep, midFusion]; omega
  have hr : ((clauseStep φ j p - midFusion φ - 1) % 3).toNat = p := by
    simp only [clauseStep, midFusion]; omega
  simp only [clauseOf, hq, hj, hr]

theorem mem_of_clauseOf (φ : Cnf) (k : Int) (c : Clause) (p : Nat)
    (h : clauseOf φ k = some (c, p)) : c ∈ φ.clauses := by
  simp only [clauseOf] at h
  split at h
  · exact absurd h (by simp)
  · next c' hc =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact List.mem_of_getElem? hc

/-- Every clause step names a clause: the quotient lands inside the list. -/
theorem clauseOf_isSome (φ : Cnf) (k : Int) (hlo : midFusion φ < k) (hhi : k < fusionTop φ) :
    ∃ c p, p < 3 ∧ clauseOf φ k = some (c, p) := by
  have hlt : ((k - midFusion φ - 1) / 3).toNat < φ.clauses.length := by
    simp only [midFusion, fusionTop] at hlo hhi ⊢; omega
  obtain ⟨c, hc⟩ : ∃ c, φ.clauses[((k - midFusion φ - 1) / 3).toNat]? = some c :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  refine ⟨c, ((k - midFusion φ - 1) % 3).toNat, by omega, ?_⟩
  simp only [clauseOf, hc]

-- ============================================================
-- Nodes, requirements, sons
-- ============================================================

/-- The nodes the map builds at step `k`. -/
def mapNodes (φ : Cnf) (k : Int) : List NodeId :=
  if k < 0 then []
  else if stepCount φ ≤ k then []
  else if k = 0 then [⟨k, 0⟩]
  else if k = midFusion φ then [⟨k, 0⟩]
  else if fusionTop φ ≤ k then [⟨k, 0⟩]
  else [⟨k, 0⟩, ⟨k, 1⟩]

/-- The requirement function — the only channel from the map to the proofs.
Total and uniform, as `lean_project`'s `CnfMap.reqOfCnf`: it does not check the index. -/
def reqOf (φ : Cnf) (d : NodeId) : List NodeId :=
  if d.step ≤ 0 then []
  else if d.step < midFusion φ then
    if d.step % 2 = 1 then []
    else [{ step := d.step - 1, index := 1 - d.index }]
  else if d.step = midFusion φ then []
  else if fusionTop φ ≤ d.step then []
  else
    match clauseOf φ d.step with
    | none => []
    | some (c, p) => [{ step := (litAt c p).binStep, index := d.index }]

/-- The sons the map links. A positive variable node links only to the
negation node it agrees with (`add_var!`'s `add_son!`); every other node links
to every node of the next step. -/
def sonsOfMap (φ : Cnf) (d : NodeId) : List NodeId :=
  if 0 < d.step ∧ d.step < midFusion φ ∧ d.step % 2 = 1 then
    [{ step := d.step + 1, index := 1 - d.index }]
  else mapNodes φ (d.step + 1)

-- ============================================================
-- The prohibited windows
-- ============================================================

/-- `k` is the third literal step of some clause. -/
def isL3 (φ : Cnf) (k : Int) : Bool :=
  decide (midFusion φ < k) && decide (k < fusionTop φ) && decide ((k - midFusion φ - 1) % 3 = 2)

/-- **The disjunction.** A path node is prohibited when it stands at the third
step of a clause and its whole window is `(0, 0, 0)`. -/
def isProhibited (φ : Cnf) (w : PathNodeId) : Bool :=
  isL3 φ w.id.step && w.id.index == 0
    && w.parent_id == some ⟨w.id.step - 1, 0⟩
    && w.gparent_id == some ⟨w.id.step - 2, 0⟩

/-- The window `(L1, L2, L3)` of clause `j` with values `b₁ b₂ b₃`. -/
def clauseWindow (φ : Cnf) (j : Nat) (b1 b2 b3 : Int) : PathNodeId :=
  { id := ⟨clauseStep φ j 2, b3⟩
    parent_id := some ⟨clauseStep φ j 1, b2⟩
    gparent_id := some ⟨clauseStep φ j 0, b1⟩ }

/-- The prohibited windows as a list, one per clause — what Julia stores in
`prohibited_windows`. -/
def prohibitedList (φ : Cnf) : List PathNodeId :=
  (List.range φ.clauses.length).map fun j => clauseWindow φ j 0 0 0

/-- **Only the all-false window of a clause is prohibited.** -/
theorem clauseWindow_prohibited_iff (φ : Cnf) (j : Nat) (hj : j < φ.clauses.length)
    (b1 b2 b3 : Int) :
    isProhibited φ (clauseWindow φ j b1 b2 b3) = true ↔ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  have hL3 : isL3 φ (clauseStep φ j 2) = true := by
    have a : midFusion φ < clauseStep φ j 2 := by simp only [midFusion, clauseStep]; omega
    have b : clauseStep φ j 2 < fusionTop φ := by simp only [fusionTop, clauseStep]; omega
    have c : (clauseStep φ j 2 - midFusion φ - 1) % 3 = 2 := by
      simp only [midFusion, clauseStep]; omega
    simp only [isL3, a, b, c, decide_true, Bool.and_self]
  have e1 : clauseStep φ j 2 - 1 = clauseStep φ j 1 := by simp only [clauseStep]; omega
  have e2 : clauseStep φ j 2 - 2 = clauseStep φ j 0 := by simp only [clauseStep]; omega
  simp only [isProhibited, clauseWindow, hL3, e1, e2, Bool.true_and, Bool.and_eq_true,
    beq_iff_eq, Option.some.injEq, NodeId.mk.injEq, true_and]
  exact ⟨fun ⟨⟨h3, h2⟩, h1⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h3, h2⟩, h1⟩⟩

/-- The predicate and the list agree: `isProhibited` is exactly membership in
what Julia stores. -/
theorem isProhibited_iff_mem (φ : Cnf) (w : PathNodeId) :
    isProhibited φ w = true ↔ w ∈ prohibitedList φ := by
  constructor
  · intro h
    obtain ⟨⟨s, i⟩, par, gp⟩ := w
    simp only [isProhibited, isL3, midFusion, fusionTop, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hmod⟩, hidx⟩, hpar⟩, hgp⟩ := h
    have hlo := of_decide_eq_true hlo
    have hhi := of_decide_eq_true hhi
    have hmod := of_decide_eq_true hmod
    subst hidx hpar hgp
    simp only [prohibitedList, List.mem_map, List.mem_range]
    refine ⟨((s - 2 * (φ.nVars : Int) - 2) / 3).toNat, by omega, ?_⟩
    simp only [clauseWindow, clauseStep, PathNodeId.mk.injEq, Option.some.injEq,
      NodeId.mk.injEq, and_true]
    repeat' constructor
    all_goals omega
  · intro h
    simp only [prohibitedList, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, rfl⟩ := h
    exact (clauseWindow_prohibited_iff φ j hj 0 0 0).mpr ⟨rfl, rfl, rfl⟩

-- ============================================================
-- What `reqOf` reduces to at each kind of step
-- ============================================================

theorem reqOf_var (φ : Cnf) (d : NodeId) (v : Nat) (hv : v < φ.nVars)
    (h : d.step = varStep v) : reqOf φ d = [] := by
  have h0 : ¬ d.step ≤ 0 := by rw [h]; simp only [varStep]; omega
  have h1 : d.step < midFusion φ := by rw [h]; simp only [varStep, midFusion]; omega
  have h2 : d.step % 2 = 1 := by rw [h]; simp only [varStep]; omega
  simp only [reqOf, if_neg h0, if_pos h1, if_pos h2]

/-- Standing on `"!v=i"` forces standing on `"v=1-i"`. -/
theorem reqOf_neg (φ : Cnf) (d : NodeId) (v : Nat) (hv : v < φ.nVars)
    (h : d.step = negStep v) :
    reqOf φ d = [{ step := varStep v, index := 1 - d.index }] := by
  have h0 : ¬ d.step ≤ 0 := by rw [h]; simp only [negStep]; omega
  have h1 : d.step < midFusion φ := by rw [h]; simp only [negStep, midFusion]; omega
  have h2 : ¬ d.step % 2 = 1 := by rw [h]; simp only [negStep]; omega
  have e : d.step - 1 = varStep v := by rw [h]; simp only [negStep, varStep]; omega
  simp only [reqOf, if_neg h0, if_pos h1, if_neg h2, e]

/-- Standing on `Lₚ = b` of clause `j` forces the literal `lₚ` to have value `b`. -/
theorem reqOf_clause (φ : Cnf) (d : NodeId) (j p : Nat) (c : Clause) (hp : p < 3)
    (hjlt : j < φ.clauses.length) (hj : φ.clauses[j]? = some c)
    (h : d.step = clauseStep φ j p) :
    reqOf φ d = [{ step := (litAt c p).binStep, index := d.index }] := by
  have h0 : ¬ d.step ≤ 0 := by rw [h]; simp only [clauseStep]; omega
  have h1 : ¬ d.step < midFusion φ := by rw [h]; simp only [clauseStep, midFusion]; omega
  have h2 : ¬ d.step = midFusion φ := by rw [h]; simp only [clauseStep, midFusion]; omega
  have h3 : ¬ fusionTop φ ≤ d.step := by rw [h]; simp only [clauseStep, fusionTop]; omega
  simp only [reqOf, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
  rw [h, clauseOf_clauseStep φ j p c hp hj]

theorem reqOf_nonpos (φ : Cnf) (d : NodeId) (h : d.step ≤ 0) : reqOf φ d = [] := by
  unfold reqOf; rw [if_pos h]

theorem reqOf_mid (φ : Cnf) (d : NodeId) (h : d.step = midFusion φ) : reqOf φ d = [] := by
  have h0 : ¬ d.step ≤ 0 := by rw [h]; simp only [midFusion]; omega
  have h1 : ¬ d.step < midFusion φ := by rw [h]; omega
  unfold reqOf; rw [if_neg h0, if_neg h1, if_pos h]

theorem reqOf_above (φ : Cnf) (d : NodeId) (h : fusionTop φ ≤ d.step) : reqOf φ d = [] := by
  have h0 : ¬ d.step ≤ 0 := by simp only [fusionTop] at h; omega
  have h1 : ¬ d.step < midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
  have h2 : ¬ d.step = midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
  unfold reqOf; rw [if_neg h0, if_neg h1, if_neg h2, if_pos h]

-- ============================================================
-- The shape of `mapNodes`
-- ============================================================

/-- A fusion step (root, middle or top) has the single node `⟨k, 0⟩`. -/
theorem mapNodes_fusion (φ : Cnf) (k : Int)
    (h : k = 0 ∨ k = midFusion φ ∨ (fusionTop φ ≤ k ∧ k < stepCount φ)) :
    mapNodes φ k = [⟨k, 0⟩] := by
  have h0 : ¬ k < 0 := by simp only [midFusion, fusionTop] at h; omega
  have hc : ¬ stepCount φ ≤ k := by
    simp only [midFusion, fusionTop, stepCount] at h ⊢; omega
  unfold mapNodes
  rw [if_neg h0, if_neg hc]
  by_cases hz : k = 0
  · rw [if_pos hz]
  · rw [if_neg hz]
    by_cases hm : k = midFusion φ
    · rw [if_pos hm]
    · rw [if_neg hm, if_pos (by omega)]

/-- Every other step of the map has both values. -/
theorem mapNodes_two (φ : Cnf) (k : Int) (h0 : 0 < k) (hm : k ≠ midFusion φ)
    (ht : k < fusionTop φ) : mapNodes φ k = [⟨k, 0⟩, ⟨k, 1⟩] := by
  have hn : ¬ k < 0 := by omega
  have hc : ¬ stepCount φ ≤ k := by simp only [fusionTop, stepCount] at ht ⊢; omega
  unfold mapNodes
  rw [if_neg hn, if_neg hc, if_neg (by omega), if_neg hm, if_neg (by omega)]

/-- Every node the map builds at a step reports that step. -/
theorem mapNodes_step (φ : Cnf) (k : Int) (d : NodeId) (h : d ∈ mapNodes φ k) : d.step = k := by
  unfold mapNodes at h
  split at h
  · exact absurd h List.not_mem_nil
  · split at h
    · exact absurd h List.not_mem_nil
    · split at h
      · rcases List.mem_singleton.mp h with rfl; rfl
      · split at h
        · rcases List.mem_singleton.mp h with rfl; rfl
        · split at h
          · rcases List.mem_singleton.mp h with rfl; rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl <;> rfl

/-- The index of a node of a two-valued step is `0` or `1`. -/
theorem mapNodes_index (φ : Cnf) (k : Int) (d : NodeId) (h : d ∈ mapNodes φ k) :
    d.index = 0 ∨ d.index = 1 := by
  unfold mapNodes at h
  split at h
  · exact absurd h List.not_mem_nil
  · split at h
    · exact absurd h List.not_mem_nil
    · split at h
      · rcases List.mem_singleton.mp h with rfl; exact Or.inl rfl
      · split at h
        · rcases List.mem_singleton.mp h with rfl; exact Or.inl rfl
        · split at h
          · rcases List.mem_singleton.mp h with rfl; exact Or.inl rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl

/-- **A son of a map node is a map node, one step up.** The crossed link of a positive variable
node lands on `1 - i`, and `i ∈ {0,1}` because the node is on the map. -/
theorem sonsOfMap_subset (φ : Cnf) (d : NodeId) (hd : d ∈ mapNodes φ d.step) :
    ∀ s ∈ sonsOfMap φ d, s ∈ mapNodes φ (d.step + 1) := by
  intro s hs
  unfold sonsOfMap at hs
  split at hs
  · rename_i hvar
    obtain ⟨hpos, hlt, hodd⟩ := hvar
    rcases List.mem_singleton.mp hs with rfl
    have hi := mapNodes_index φ _ d hd
    rw [mapNodes_two φ (d.step + 1) (by omega) (by simp only [midFusion] at hlt ⊢; omega)
      (by simp only [midFusion, fusionTop] at hlt ⊢; omega)]
    rcases hi with h | h <;> simp [h]
  · exact hs

-- ============================================================
-- The two obligations `Reachable.up` states
-- ============================================================

/-- **At most one requirement per node.** The classic `Functional` is a
corollary with no hypothesis at all. -/
theorem reqOf_length_le_one (φ : Cnf) (d : NodeId) : (reqOf φ d).length ≤ 1 := by
  unfold reqOf
  split
  · simp
  · split
    · split <;> simp
    · split
      · simp
      · split
        · simp
        · split <;> simp

theorem reqOf_functional (φ : Cnf) (d : NodeId) :
    ∀ r₁ ∈ reqOf φ d, ∀ r₂ ∈ reqOf φ d, r₁ = r₂ := by
  intro r₁ h₁ r₂ h₂
  have hl := reqOf_length_le_one φ d
  match hr : reqOf φ d with
  | [] => rw [hr] at h₁; exact absurd h₁ List.not_mem_nil
  | [x] =>
    rw [hr] at h₁ h₂
    rw [List.mem_singleton.mp h₁, List.mem_singleton.mp h₂]
  | _ :: _ :: _ => rw [hr] at hl; simp at hl

/-- Requirements point strictly backwards. -/
theorem reqOf_backward (φ : Cnf) (hb : Bounded φ) (d : NodeId) :
    ∀ r ∈ reqOf φ d, r.step < d.step := by
  intro r hr
  unfold reqOf at hr
  split at hr
  · exact absurd hr List.not_mem_nil
  · split at hr
    · split at hr
      · exact absurd hr List.not_mem_nil
      · rcases List.mem_singleton.mp hr with rfl
        show d.step - 1 < d.step
        omega
    · split at hr
      · exact absurd hr List.not_mem_nil
      · split at hr
        · exact absurd hr List.not_mem_nil
        · next hlo hne _ =>
          split at hr
          · exact absurd hr List.not_mem_nil
          · next c p hc =>
            rcases List.mem_singleton.mp hr with rfl
            have hcm := mem_of_clauseOf φ d.step c p hc
            obtain ⟨b1, b2, b3⟩ := hb c hcm
            have hv : (litAt c p).v < φ.nVars := by
              unfold litAt; split <;> assumption
            have := (lit_step_bounds φ (litAt c p) hv).2
            show (litAt c p).binStep < d.step
            omega

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSatBin.GraphMap.CnfMapBin.reqOf_backward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqOf_backward

/-- info: 'AbsSatBin.GraphMap.CnfMapBin.reqOf_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqOf_functional

/-- info: 'AbsSatBin.GraphMap.CnfMapBin.isProhibited_iff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isProhibited_iff_mem

/-- info: 'AbsSatBin.GraphMap.CnfMapBin.clauseWindow_prohibited_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clauseWindow_prohibited_iff

/-- info: 'AbsSatBin.GraphMap.CnfMapBin.reqOf_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqOf_clause

end AbsSatBin.GraphMap.CnfMapBin
