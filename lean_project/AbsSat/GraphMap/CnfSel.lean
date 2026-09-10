-- lean_project/AbsSat/GraphMap/CnfSel.lean
import AbsSat.GraphMap.CnfMap

/-!
# The other direction, at the level of the map

Given an assignment, read the selection it names: the node carrying its truth
value at each variable step, the matching node in the negation block, and at a
clause step the row spelling the three literals' values.

Two facts, and the split between them is worth seeing:

* `reqSat_selOfAssign` needs **no** satisfiability. Any assignment's selection
  satisfies every requirement of every node it picks — that is just the map's
  bookkeeping being consistent.
* `selOfAssign_onMap` is where `Sat` enters, and it enters in exactly one
  place: a satisfied clause has a row other than `000`, which is the one row
  the map does not build.

That is the mirror image of the decode direction, where `ReqSatisfying` does
the work and being on the map supplies the other half.

**Scope.** This is the map-level half of completeness only. Nothing here claims
the selection is an `IsChain` in a graph the machine holds; lifting it through
the filtering is L2⊇, which is the open problem.
-/

namespace AbsSat.GraphMap.CnfSel

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap

/-- A bit as an `Int`. Named so the row proofs are case analyses on `Bool`
rather than `if`-juggling, which keeps `omega` and `decide` happy. -/
def bit (b : Bool) : Int := if b then 1 else 0

theorem bit_true : bit true = 1 := rfl
theorem bit_false : bit false = 0 := rfl

/-- The clause row an assignment names: the three literals' truth values as a
3-bit index, which is exactly `add_gate_case!`'s `4b₁+2b₂+b₃`. -/
def rowOf (a : Assign) (c : Clause) : Int :=
  4 * bit (litVal a c.l1) + 2 * bit (litVal a c.l2) + bit (litVal a c.l3)

theorem rowOf_le (a : Assign) (c : Clause) : rowOf a c ≤ 7 := by
  cases h1 : litVal a c.l1 <;> cases h2 : litVal a c.l2 <;> cases h3 : litVal a c.l3 <;>
    simp only [rowOf, h1, h2, h3, bit_true, bit_false] <;> decide

/-- **Where satisfiability enters, and the only place it does.** A satisfied
clause names a row other than `000` — the one row the map does not build. -/
theorem rowOf_pos (a : Assign) (c : Clause) (h : SatClause a c) : 1 ≤ rowOf a c := by
  cases h1 : litVal a c.l1 <;> cases h2 : litVal a c.l2 <;> cases h3 : litVal a c.l3 <;>
    simp only [rowOf, h1, h2, h3, bit_true, bit_false] <;>
    first
      | decide
      | (exfalso; rcases h with hh | hh | hh <;> simp only [h1, h2, h3] at hh <;>
          exact Bool.noConfusion hh)

theorem b1_rowOf (a : Assign) (c : Clause) : b1 (rowOf a c) = bit (litVal a c.l1) := by
  cases h1 : litVal a c.l1 <;> cases h2 : litVal a c.l2 <;> cases h3 : litVal a c.l3 <;>
    simp only [rowOf, b1, h1, h2, h3, bit_true, bit_false] <;> decide

theorem b2_rowOf (a : Assign) (c : Clause) : b2 (rowOf a c) = bit (litVal a c.l2) := by
  cases h1 : litVal a c.l1 <;> cases h2 : litVal a c.l2 <;> cases h3 : litVal a c.l3 <;>
    simp only [rowOf, b2, h1, h2, h3, bit_true, bit_false] <;> decide

theorem b3_rowOf (a : Assign) (c : Clause) : b3 (rowOf a c) = bit (litVal a c.l3) := by
  cases h1 : litVal a c.l1 <;> cases h2 : litVal a c.l2 <;> cases h3 : litVal a c.l3 <;>
    simp only [rowOf, b3, h1, h2, h3, bit_true, bit_false] <;> decide

-- ============================================================
-- Bit arithmetic
-- ============================================================

theorem one_sub_bit_not (b : Bool) : 1 - bit (!b) = bit b := by cases b <;> decide

theorem bit_eq_one_iff (b : Bool) : (bit b == 1) = b := by cases b <;> decide

-- ============================================================
-- The selection an assignment names
-- ============================================================

/-- Read an assignment as a walk through the map: the node carrying a
variable's truth value at its own step, the matching node of the negation
block, and at a clause step the row spelling the three literals' values. -/
def selOfAssign (φ : Cnf) (a : Assign) (k : Int) : NodeId :=
  if k < 0 then ⟨k, 0⟩
  else if k < litBlock φ then
    if k % 2 = 0 then ⟨k, bit (a (k / 2).toNat)⟩
    else ⟨k, bit (!(a ((k - 1) / 2).toNat))⟩
  else if k ≤ litBlock φ then ⟨k, 0⟩
  else if fusionTop φ ≤ k then ⟨k, 0⟩
  else
    match clauseAt φ k with
    | none => ⟨k, 0⟩
    | some c => ⟨k, rowOf a c⟩

theorem selOfAssign_step (φ : Cnf) (a : Assign) (k : Int) :
    (selOfAssign φ a k).step = k := by
  unfold selOfAssign
  split
  · rfl
  · split
    · split <;> rfl
    · split
      · rfl
      · split
        · rfl
        · cases clauseAt φ k <;> rfl

theorem selOfAssign_var (φ : Cnf) (a : Assign) (v : Nat) (hv : v < φ.nVars) :
    selOfAssign φ a (varStep v) = ⟨varStep v, bit (a v)⟩ := by
  have h0 : ¬ (varStep v < 0) := by simp only [varStep]; omega
  have h1 : varStep v < litBlock φ := by simp only [varStep, litBlock]; omega
  have h2 : varStep v % 2 = 0 := by simp only [varStep]; omega
  have h3 : (varStep v / 2).toNat = v := by simp only [varStep]; omega
  simp only [selOfAssign, if_neg h0, if_pos h1, if_pos h2, h3]

theorem selOfAssign_neg (φ : Cnf) (a : Assign) (v : Nat) (hv : v < φ.nVars) :
    selOfAssign φ a (negStep v) = ⟨negStep v, bit (!(a v))⟩ := by
  have h0 : ¬ (negStep v < 0) := by simp only [negStep]; omega
  have h1 : negStep v < litBlock φ := by simp only [negStep, litBlock]; omega
  have h2 : ¬ (negStep v % 2 = 0) := by simp only [negStep]; omega
  have h3 : ((negStep v - 1) / 2).toNat = v := by simp only [negStep]; omega
  simp only [selOfAssign, if_neg h0, if_pos h1, if_neg h2, h3]

/-- The two variable cases in one: at a literal's own step the selection
carries that literal's truth value. -/
theorem selOfAssign_lit (φ : Cnf) (a : Assign) (l : Lit) (hl : l.v < φ.nVars) :
    selOfAssign φ a l.step = ⟨l.step, bit (litVal a l)⟩ := by
  cases hp : l.pos with
  | true =>
    rw [varStep_eq l hp, selOfAssign_var φ a l.v hl]
    simp [litVal, hp]
  | false =>
    rw [negStep_eq l hp, selOfAssign_neg φ a l.v hl]
    simp [litVal, hp]

theorem selOfAssign_clause (φ : Cnf) (a : Assign) (j : Nat) (c : Clause)
    (hjlt : j < φ.clauses.length) (hj : φ.clauses[j]? = some c) :
    selOfAssign φ a (clauseStep φ j) = ⟨clauseStep φ j, rowOf a c⟩ := by
  have h0 : ¬ (clauseStep φ j < 0) := by simp only [clauseStep]; omega
  have h1 : ¬ (clauseStep φ j < litBlock φ) := by simp only [clauseStep, litBlock]; omega
  have h2 : ¬ (clauseStep φ j ≤ litBlock φ) := by simp only [clauseStep, litBlock]; omega
  have h3 : ¬ (fusionTop φ ≤ clauseStep φ j) := by simp only [clauseStep, fusionTop]; omega
  have h4 : clauseAt φ (clauseStep φ j) = some c := by
    simp only [clauseAt, clauseStep]
    have he : (2 * (φ.nVars : Int) + 1 + (j : Int) - 2 * (φ.nVars : Int) - 1).toNat = j := by
      omega
    rw [he]; exact hj
  simp only [selOfAssign, if_neg h0, if_neg h1, if_neg h2, if_neg h3, h4]

-- ============================================================
-- The two halves, and the split between them
-- ============================================================

/-- **The requirements are satisfied by *any* assignment's selection.** Note
the absence of `Sat`: this is the map's bookkeeping being consistent with
itself, nothing more. Satisfiability plays no part until the next theorem. -/
theorem reqSat_selOfAssign (φ : Cnf) (hwf : WF φ) (a : Assign) (k : Int) :
    ∀ req ∈ reqOfCnf φ (selOfAssign φ a k), selOfAssign φ a req.step = req := by
  intro req hreq
  have hstep : (selOfAssign φ a k).step = k := selOfAssign_step φ a k
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, hjlt, rfl⟩ | h
  · rw [reqOfCnf_below φ _ (by rw [hstep]; exact h)] at hreq
    exact absurd hreq List.not_mem_nil
  · rw [reqOfCnf_var φ _ v hv hstep] at hreq
    exact absurd hreq List.not_mem_nil
  · have hidx : (selOfAssign φ a (negStep v)).index = bit (!(a v)) := by
      rw [selOfAssign_neg φ a v hv]
    rw [reqOfCnf_neg φ _ v hv hstep, hidx] at hreq
    rcases List.mem_singleton.mp hreq with rfl
    show selOfAssign φ a (varStep v) = _
    rw [selOfAssign_var φ a v hv, one_sub_bit_not]
  · rw [reqOfCnf_fusion1 φ _ (by rw [hstep]; exact h)] at hreq
    exact absurd hreq List.not_mem_nil
  · have hj : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hjlt
    have hidx : (selOfAssign φ a (clauseStep φ j)).index = rowOf a φ.clauses[j] := by
      rw [selOfAssign_clause φ a j _ hjlt hj]
    rw [reqOfCnf_clause φ _ j _ hjlt hj hstep, hidx, b1_rowOf, b2_rowOf, b3_rowOf] at hreq
    obtain ⟨⟨h1, h2, h3⟩, _⟩ := hwf φ.clauses[j] (List.mem_of_getElem? hj)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreq
    rcases hreq with rfl | rfl | rfl
    · show selOfAssign φ a φ.clauses[j].l1.step = _
      exact selOfAssign_lit φ a _ h1
    · show selOfAssign φ a φ.clauses[j].l2.step = _
      exact selOfAssign_lit φ a _ h2
    · show selOfAssign φ a φ.clauses[j].l3.step = _
      exact selOfAssign_lit φ a _ h3
  · rw [reqOfCnf_above φ _ (by rw [hstep]; exact h)] at hreq
    exact absurd hreq List.not_mem_nil

/-- **And this is where `Sat` enters, in exactly one place.** A satisfied
clause names a row other than `000` — the one row the map does not build — so
the selection lands on nodes the map actually contains. -/
theorem selOfAssign_onMap (φ : Cnf) (a : Assign) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k < stepCount φ) :
    selOfAssign φ a k ∈ mapNodes φ k := by
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, hjlt, rfl⟩ | h
  · omega
  · rw [selOfAssign_var φ a v hv,
      mapNodes_var φ _ (by simp only [varStep]; omega) (by simp only [varStep, litBlock]; omega)]
    cases hb : a v <;> simp [bit_true, bit_false]
  · rw [selOfAssign_neg φ a v hv,
      mapNodes_var φ _ (by simp only [negStep]; omega) (by simp only [negStep, litBlock]; omega)]
    cases hb : a v <;> simp [bit_true, bit_false]
  · rw [mapNodes_fusion1 φ _ h]
    have h0' : ¬ (k < 0) := by rw [h]; simp only [litBlock]; omega
    have h1' : ¬ (k < litBlock φ) := by rw [h]; omega
    have h2' : k ≤ litBlock φ := by rw [h]; omega
    simp only [selOfAssign, if_neg h0', if_neg h1', if_pos h2']
    exact List.mem_cons_self
  · have hj : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hjlt
    have hcm : φ.clauses[j] ∈ φ.clauses := List.mem_of_getElem? hj
    have hrlo := rowOf_pos a φ.clauses[j] (hsat _ hcm)
    have hrhi := rowOf_le a φ.clauses[j]
    rw [selOfAssign_clause φ a j _ hjlt hj, mapNodes_clause φ j hjlt _ rfl]
    have hr : rowOf a φ.clauses[j] = 1 ∨ rowOf a φ.clauses[j] = 2 ∨ rowOf a φ.clauses[j] = 3
        ∨ rowOf a φ.clauses[j] = 4 ∨ rowOf a φ.clauses[j] = 5 ∨ rowOf a φ.clauses[j] = 6
        ∨ rowOf a φ.clauses[j] = 7 := by omega
    rcases hr with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> simp
  · rw [mapNodes_fusionTop φ _ h hk]
    have h0' : ¬ (k < 0) := by simp only [fusionTop] at h; omega
    have h1' : ¬ (k < litBlock φ) := by simp only [fusionTop, litBlock] at h ⊢; omega
    have h2' : ¬ (k ≤ litBlock φ) := by simp only [fusionTop, litBlock] at h ⊢; omega
    simp only [selOfAssign, if_neg h0', if_neg h1', if_neg h2', if_pos h]
    exact List.mem_cons_self

-- ============================================================
-- The map's own edges, and that the branch follows them
-- ============================================================

/-!
`add_var!` links the two positive nodes of a variable to the negation block
**crossed**: `"v=0"` has son `"!v=1"` and `"v=1"` has son `"!v=0"`. Everywhere
else the map is complete between consecutive steps — the next block's nodes are
linked to every node of the previous one.

So the son relation is two lines of arithmetic, and the point of writing it
down is `selOfAssign_son` below: the branch an assignment names is not a
sequence someone chose, it is a **path along the map's own edges**, which is
what the driver walks.
-/

def mapSons (φ : Cnf) (k : Int) (i : Int) : List NodeId :=
  if k < 0 then []
  else if k < litBlock φ then
    if k % 2 = 0 then [⟨k + 1, 1 - i⟩] else mapNodes φ (k + 1)
  else mapNodes φ (k + 1)

theorem bit_not (b : Bool) : bit (!b) = 1 - bit b := by cases b <;> decide

theorem mapSons_var (φ : Cnf) (v : Nat) (hv : v < φ.nVars) (i : Int) :
    mapSons φ (varStep v) i = [⟨varStep v + 1, 1 - i⟩] := by
  have h0 : ¬ (varStep v < 0) := by simp only [varStep]; omega
  have h1 : varStep v < litBlock φ := by simp only [varStep, litBlock]; omega
  have h2 : varStep v % 2 = 0 := by simp only [varStep]; omega
  simp only [mapSons, if_neg h0, if_pos h1, if_pos h2]

theorem mapSons_other (φ : Cnf) (k : Int) (i : Int) (h0 : 0 ≤ k)
    (h : ¬ (k < litBlock φ ∧ k % 2 = 0)) : mapSons φ k i = mapNodes φ (k + 1) := by
  have hneg : ¬ (k < 0) := by omega
  by_cases h1 : k < litBlock φ
  · have h2 : ¬ (k % 2 = 0) := fun hc => h ⟨h1, hc⟩
    simp only [mapSons, if_neg hneg, if_pos h1, if_neg h2]
  · simp only [mapSons, if_neg hneg, if_neg h1]

/-- **The assignment's branch is a path along the map's own edges.** Whatever
the driver does with the rest of the map, this sequence of nodes is one it can
walk: each is a son of the one before. -/
theorem selOfAssign_son (φ : Cnf) (a : Assign) (hsat : Sat a φ) (k : Int)
    (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ) :
    selOfAssign φ a (k + 1) ∈ mapSons φ k (selOfAssign φ a k).index := by
  by_cases hvar : k < litBlock φ ∧ k % 2 = 0
  · obtain ⟨hlt, hpar⟩ := hvar
    obtain ⟨v, hv, rfl⟩ : ∃ v, v < φ.nVars ∧ k = varStep v := by
      refine ⟨(k / 2).toNat, ?_, ?_⟩
      · simp only [litBlock] at hlt
        omega
      · simp only [varStep]
        omega
    have hnext : varStep v + 1 = negStep v := by simp only [varStep, negStep]
    simp only [selOfAssign_var φ a v hv, mapSons_var φ v hv, hnext,
      selOfAssign_neg φ a v hv, bit_not, List.mem_singleton]
  · rw [mapSons_other φ k _ h0 hvar]
    exact selOfAssign_onMap φ a hsat (k + 1) (by omega) hk

/-- info: 'AbsSat.GraphMap.CnfSel.reqSat_selOfAssign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqSat_selOfAssign

/-- info: 'AbsSat.GraphMap.CnfSel.selOfAssign_onMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selOfAssign_onMap

/-- info: 'AbsSat.GraphMap.CnfSel.rowOf_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms rowOf_pos

end AbsSat.GraphMap.CnfSel
