import AbsSat.SatMachine.Model.Problem
import AbsSat.SatMachine.Model.Axioms
import AbsSat.SatMachine.Model.Soundness

namespace AbsSat.SatMachine.Model

open AbsSat.SatMachine.Model

/--
  Completeness Theorem: if a valid solution exists (witnessed by a
  layer-respecting sequence of choices, see `Solvable`), the machine finds
  it. This no longer relies on any axiom: `run_pure_complete` is proved by
  induction in Axioms.lean directly from the fact that `evolve_path_nodes`
  is exhaustive (it filters, it never picks just one).
-/
theorem completeness_theorem (gmap : PureGMap) :
  Solvable gmap -> ∃ p, list_contains (run_pure gmap) p = true := by
  intro h
  cases h with
  | exists_choices choices h_valid =>
    exact ⟨fold_choices choices { visited_nodes := [] },
      (list_contains_iff_mem _ _).mpr (run_pure_complete gmap choices h_valid)⟩

end AbsSat.SatMachine.Model
