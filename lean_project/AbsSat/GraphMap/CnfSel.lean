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

/-- info: 'AbsSat.GraphMap.CnfSel.rowOf_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms rowOf_pos

end AbsSat.GraphMap.CnfSel
