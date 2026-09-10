-- lean_project/AbsSat/GraphMap/CnfMap.lean
import AbsSat.Cnf.Formula
import AbsSat.Utils.Alias

/-!
# The map of a CNF, as arithmetic

`ImportCnf` builds a `GMap` from a DIMACS file, and it is `IO` — not because
the construction needs effects, but because `MapColVars` keeps the variable
name table in an `IO.Ref`. A `GMap` is also `Std.HashMap`-based, which would be
as painful to reason about as `GPath` was before `GPathM` existed.

**The proof side does not need a `GMap` at all.** The map reaches `Reachable`,
`L1`, `L1_cor` and `MapChain` through exactly one channel — the function
`reqOf : NodeId → List NodeId` — and the encoding is pure arithmetic on
`step`/`index`. So the pure mirror of the map is this module: `stepCount`,
`mapNodes`, `reqOfCnf`, with no data structure anywhere, and a differential
band ties it to `load_import!` the way `MirrorTest` ties `GPathM` to `GPath`.

## The encoding it reproduces

For `n` variables and `m` clauses, `GraphMap.add_var!` / `add_gate_case!` /
`make_fusion_node!` build:

| step | nodes |
|---|---|
| `2v` | `⟨2v,0⟩` (`"v=0"`), `⟨2v,1⟩` (`"v=1"`) — no requirements |
| `2v+1` | `⟨2v+1,i⟩` (`"!v=i"`), requiring `⟨2v, 1-i⟩` |
| `2n` | one `"FusionNode"` |
| `2n+1+j` | seven `⟨·,r⟩` for `r ∈ 1..7`, `r = 4b₁+2b₂+b₃`, requiring `⟨lₚ.step, bₚ⟩` |
| `2n+1+m` | one `"FusionNode"` |

so `stepCount = 2n + m + 2`.

**Note the deliberate asymmetry.** `reqOfCnf` is *total and uniform* across a
clause step: it does not check that the index is in `1..7`. Index `0` yields
exactly the all-literals-false row — the one row the map omits. Keeping that
check out of `reqOfCnf` is what makes `Functional` and `Backward` free of range
hypotheses; the omission of row `000` lives entirely in `mapNodes`, which is
where the decode argument reaches for it.
-/

namespace AbsSat.GraphMap.CnfMap

open AbsSat.Utils.Alias
open AbsSat.Cnf

-- ============================================================
-- The step arithmetic
-- ============================================================

def varStep (v : Nat) : Int := 2 * (v : Int)
def negStep (v : Nat) : Int := 2 * (v : Int) + 1

def litBlock (φ : Cnf) : Int := 2 * (φ.nVars : Int)
def clauseStep (φ : Cnf) (j : Nat) : Int := 2 * (φ.nVars : Int) + 1 + (j : Int)
def fusionTop (φ : Cnf) : Int := 2 * (φ.nVars : Int) + 1 + (φ.clauses.length : Int)
def stepCount (φ : Cnf) : Int := 2 * (φ.nVars : Int) + (φ.clauses.length : Int) + 2

theorem varStep_eq (l : Lit) (h : l.pos = true) : l.step = varStep l.v := by
  simp [Lit.step, varStep, h]

theorem negStep_eq (l : Lit) (h : l.pos = false) : l.step = negStep l.v := by
  simp [Lit.step, negStep, h]

-- ============================================================
-- The three bits of a clause row
-- ============================================================

def b1 (r : Int) : Int := r / 4 % 2
def b2 (r : Int) : Int := r / 2 % 2
def b3 (r : Int) : Int := r % 2

/-- **The map omits exactly the all-false row.** Every index the map does build
names at least one literal as true — this single fact is the whole content of
"the seven rows are the seven satisfying rows". -/
theorem bits_not_all_zero (r : Int) (h1 : 1 ≤ r) (h7 : r ≤ 7) :
    b1 r = 1 ∨ b2 r = 1 ∨ b3 r = 1 := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  unfold b1 b2 b3
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

-- ============================================================
-- The requirement function — the only channel to the proofs
-- ============================================================

def litReq (l : Lit) (b : Int) : NodeId := { step := l.step, index := b }

def clauseAt (φ : Cnf) (k : Int) : Option Clause :=
  φ.clauses[(k - 2 * (φ.nVars : Int) - 1).toNat]?

def reqOfCnf (φ : Cnf) (d : NodeId) : List NodeId :=
  if d.step < 0 then []
  else if d.step < litBlock φ then
    if d.step % 2 = 0 then []
    else [{ step := d.step - 1, index := 1 - d.index }]
  else if d.step ≤ litBlock φ then []
  else if fusionTop φ ≤ d.step then []
  else
    match clauseAt φ d.step with
    | none => []
    | some c => [litReq c.l1 (b1 d.index), litReq c.l2 (b2 d.index), litReq c.l3 (b3 d.index)]

/-- The nodes the map actually builds at a step. Renamed from the obvious
`nodesAt` to avoid colliding with `Hypergraph.nodesAt`. -/
def mapNodes (φ : Cnf) (k : Int) : List NodeId :=
  if k < 0 then []
  else if stepCount φ ≤ k then []
  else if k < litBlock φ then [⟨k, 0⟩, ⟨k, 1⟩]
  else if k ≤ litBlock φ then [⟨k, 0⟩]
  else if fusionTop φ ≤ k then [⟨k, 0⟩]
  else [⟨k, 1⟩, ⟨k, 2⟩, ⟨k, 3⟩, ⟨k, 4⟩, ⟨k, 5⟩, ⟨k, 6⟩, ⟨k, 7⟩]

-- ============================================================
-- Characterisation: what `reqOfCnf` reduces to at each kind of step
-- ============================================================

theorem reqOfCnf_var (φ : Cnf) (d : NodeId) (v : Nat) (hv : v < φ.nVars)
    (h : d.step = varStep v) : reqOfCnf φ d = [] := by
  have hlt : d.step < litBlock φ := by rw [h]; simp only [varStep, litBlock]; omega
  have hpos : ¬ (d.step < 0) := by rw [h]; simp only [varStep]; omega
  have hmod : d.step % 2 = 0 := by rw [h]; simp only [varStep]; omega
  simp only [reqOfCnf, if_neg hpos, if_pos hlt, if_pos hmod]

/-- **The negation block's own requirement.** This is the bridge the decode
direction walks across: standing on `"!v=1"` forces standing on `"v=0"`. -/
theorem reqOfCnf_neg (φ : Cnf) (d : NodeId) (v : Nat) (hv : v < φ.nVars)
    (h : d.step = negStep v) :
    reqOfCnf φ d = [{ step := varStep v, index := 1 - d.index }] := by
  have hlt : d.step < litBlock φ := by rw [h]; simp only [negStep, litBlock]; omega
  have hpos : ¬ (d.step < 0) := by rw [h]; simp only [negStep]; omega
  have hmod : ¬ (d.step % 2 = 0) := by rw [h]; simp only [negStep]; omega
  simp only [reqOfCnf, if_neg hpos, if_pos hlt, if_neg hmod]
  have : d.step - 1 = varStep v := by rw [h]; simp only [negStep, varStep]; omega
  rw [this]

theorem reqOfCnf_clause (φ : Cnf) (d : NodeId) (j : Nat) (c : Clause)
    (hjlt : j < φ.clauses.length) (hj : φ.clauses[j]? = some c)
    (h : d.step = clauseStep φ j) :
    reqOfCnf φ d =
      [litReq c.l1 (b1 d.index), litReq c.l2 (b2 d.index), litReq c.l3 (b3 d.index)] := by
  have hpos : ¬ (d.step < 0) := by rw [h]; simp only [clauseStep]; omega
  have hlt : ¬ (d.step < litBlock φ) := by rw [h]; simp only [clauseStep, litBlock]; omega
  have hle : ¬ (d.step ≤ litBlock φ) := by rw [h]; simp only [clauseStep, litBlock]; omega
  have htop : ¬ (fusionTop φ ≤ d.step) := by
    rw [h]; simp only [clauseStep, fusionTop]; omega
  have hidx : clauseAt φ d.step = some c := by
    simp only [clauseAt, h, clauseStep]
    have : (2 * (φ.nVars : Int) + 1 + (j : Int) - 2 * (φ.nVars : Int) - 1).toNat = j := by omega
    rw [this]; exact hj
  simp only [reqOfCnf, if_neg hpos, if_neg hlt, if_neg hle, if_neg htop, hidx]

theorem mapNodes_clause (φ : Cnf) (j : Nat) (hj : j < φ.clauses.length) (k : Int)
    (h : k = clauseStep φ j) :
    mapNodes φ k = [⟨k, 1⟩, ⟨k, 2⟩, ⟨k, 3⟩, ⟨k, 4⟩, ⟨k, 5⟩, ⟨k, 6⟩, ⟨k, 7⟩] := by
  have hpos : ¬ (k < 0) := by rw [h]; simp only [clauseStep]; omega
  have hcnt : ¬ (stepCount φ ≤ k) := by rw [h]; simp only [clauseStep, stepCount]; omega
  have hlt : ¬ (k < litBlock φ) := by rw [h]; simp only [clauseStep, litBlock]; omega
  have hle : ¬ (k ≤ litBlock φ) := by rw [h]; simp only [clauseStep, litBlock]; omega
  have htop : ¬ (fusionTop φ ≤ k) := by rw [h]; simp only [clauseStep, fusionTop]; omega
  simp only [mapNodes, if_neg hpos, if_neg hcnt, if_neg hlt, if_neg hle, if_neg htop]

/-- The range extraction the decode needs: a real clause node's index is one of
the seven the map builds. -/
theorem index_range_of_clauseNode (φ : Cnf) (j : Nat) (hj : j < φ.clauses.length)
    (d : NodeId) (hd : d ∈ mapNodes φ (clauseStep φ j)) : 1 ≤ d.index ∧ d.index ≤ 7 := by
  rw [mapNodes_clause φ j hj _ rfl] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with h | h | h | h | h | h | h <;> simp only [h] <;> exact ⟨by omega, by omega⟩

-- ============================================================
-- The two obligations `Reachable.up` states
-- ============================================================

/-- **The shape of a requirement list, decided once.** Both obligations below
read it off this; splitting the `if`-chain separately in each hypothesis does
not work, because a `split` in one hypothesis leaves the other untouched. -/
theorem reqOfCnf_shape (φ : Cnf) (d : NodeId) :
    reqOfCnf φ d = []
    ∨ reqOfCnf φ d = [{ step := d.step - 1, index := 1 - d.index }]
    ∨ ∃ c, c ∈ φ.clauses ∧ litBlock φ < d.step ∧ reqOfCnf φ d =
        [litReq c.l1 (b1 d.index), litReq c.l2 (b2 d.index), litReq c.l3 (b3 d.index)] := by
  unfold reqOfCnf
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · next hle _ =>
          cases hc : clauseAt φ d.step with
          | none => exact Or.inl rfl
          | some c =>
            refine Or.inr (Or.inr ⟨c, ?_, by omega, rfl⟩)
            simp only [clauseAt] at hc
            exact List.mem_of_getElem? hc

/-- A literal of a well-formed clause sits inside the literal block. -/
theorem lit_step_lt (φ : Cnf) (l : Lit) (h : l.v < φ.nVars) : l.step < litBlock φ := by
  simp only [Lit.step, litBlock]
  split <;> omega

/-- Requirements point strictly backwards. This is `Reachable.up`'s
`hreqs_back`, and `GraphMap.MapReqs.Backward` for the arithmetic model. -/
theorem reqOfCnf_backward (φ : Cnf) (hwf : WF φ) (d : NodeId) :
    ∀ r ∈ reqOfCnf φ d, r.step < d.step := by
  intro r hr
  rcases reqOfCnf_shape φ d with h | h | ⟨c, hcm, hblk, h⟩
  · rw [h] at hr; exact absurd hr List.not_mem_nil
  · rw [h] at hr
    rcases List.mem_singleton.mp hr with rfl
    show d.step - 1 < d.step
    omega
  · rw [h] at hr
    obtain ⟨⟨h1, h2, h3⟩, _⟩ := hwf c hcm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have key : ∀ l : Lit, l.v < φ.nVars → (litReq l (0 : Int)).step < d.step := by
      intro l hl
      show l.step < d.step
      have := lit_step_lt φ l hl
      omega
    rcases hr with rfl | rfl | rfl
    · exact key c.l1 h1
    · exact key c.l2 h2
    · exact key c.l3 h3

/-- At most one requirement per step. This is `Reachable.up`'s `hreqs_distinct`
verbatim, and `GraphMap.MapReqs.Functional` for the arithmetic model.

Reproved from scratch over `List` rather than reusing `MapReqs.NodeOk_three`:
that one is about `MapDocNode` and `Std.HashSet`, and using it would drag
`Classical.choice` into every closure downstream. -/
theorem reqOfCnf_functional (φ : Cnf) (hwf : WF φ) (d : NodeId) :
    ∀ r₁ ∈ reqOfCnf φ d, ∀ r₂ ∈ reqOfCnf φ d, r₁.step = r₂.step → r₁ = r₂ := by
  intro r₁ h₁ r₂ h₂ hs
  rcases reqOfCnf_shape φ d with h | h | ⟨c, hcm, _, h⟩
  · rw [h] at h₁; exact absurd h₁ List.not_mem_nil
  · rw [h] at h₁ h₂
    rcases List.mem_singleton.mp h₁ with rfl
    rcases List.mem_singleton.mp h₂ with rfl
    rfl
  · rw [h] at h₁ h₂
    obtain ⟨_, hd12, hd13, hd23⟩ := hwf c hcm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
      simp only [litReq] at hs ⊢ <;>
      first
        | rfl
        | exact absurd hs hd12
        | exact absurd hs hd13
        | exact absurd hs hd23
        | exact absurd hs.symm hd12
        | exact absurd hs.symm hd13
        | exact absurd hs.symm hd23

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphMap.CnfMap.reqOfCnf_backward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqOfCnf_backward

/-- info: 'AbsSat.GraphMap.CnfMap.reqOfCnf_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqOfCnf_functional

end AbsSat.GraphMap.CnfMap
