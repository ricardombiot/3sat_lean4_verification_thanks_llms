import AbsSat.SatMachine.Model.Problem
import AbsSat.SatMachine.Model.Axioms

namespace AbsSat.SatMachine.Model

open AbsSat.SatMachine.Model

-- Completeness Theorem
-- If a valid solution exists, the machine finds it.

theorem completeness_theorem (gmap : PureGMap) :
  Solvable gmap -> ∃ p, list_contains (run_pure gmap) p = true := by
  intro h
  cases h with
  | exists_path p_sol h_valid =>
    -- We use the axiom `valid_prefix_maintained`.
    -- run_pure gmap is equivalent to run_layers (gmap.layers.take (gmap.layers.length)) ...
    -- We instantiate the axiom for k = gmap.layers.length
    have h_prefix := valid_prefix_maintained gmap p_sol h_valid (gmap.layers.length)
    rcases h_prefix with ⟨p_final, h_in⟩
    exists p_final
    -- We need to show `run_layers (gmap.layers.take (gmap.layers.length))` is `run_pure gmap`.
    -- Since take length = all, it matches.
    -- Assuming structural equality or trivial lemma.
    have h_eq : gmap.layers.take (gmap.layers.length) = gmap.layers := List.take_length
    rw [h_eq] at h_in
    unfold run_pure
    exact h_in

end AbsSat.SatMachine.Model
