-- lean_project/AbsSat/SatMachine/PureProofsImproves.lean
import AbsSat.SatMachine.PureSatMachineImproves
import AbsSat.GraphPath.Model.ConservationImproves

/-!
# Bridge: `SatMachinePureImproves` ↔ `PureDriverImproves`

The mirror of `PureProofs` for the improved machine: the last row of the
timeline is exactly `pureRunW`, so what `ConservationImproves` proves about the
driver holds for `run_pure`. In particular the improved machine answers SAT on
every well-formed satisfiable formula (`completeness_improves`), with no open
hypothesis.

Soundness is not stated here. For the reference machine it rests on the open
hypothesis `ClauseStepExact` through `Decision`, which is about `pureRun`; the
improved run has the same verdicts in every instance measured, but that is not
yet a theorem.
-/

namespace AbsSat.SatMachine.PureProofsImproves

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ConservationImproves (pureRunW_ne_nil)
open AbsSat.SatMachine.PureSatMachineImproves

theorem step_pure_of_lt (m : SatMachinePureImproves)
    (h : m.current_step < (stepCount m.cnf).toNat - 1) :
    step_pure m =
      { cnf := m.cnf
        timeline := m.timeline ++ [pureAdvanceW m.cnf
          (if m.current_step < m.timeline.length then m.timeline[m.current_step]! else [])]
        current_step := m.current_step + 1 } := by
  simp only [step_pure]
  rw [if_neg (show ¬ m.current_step ≥ (stepCount m.cnf).toNat - 1 by omega)]

theorem pureStepsW_succ' (φ : Cnf) : ∀ (n : Nat) (line : PureLine),
    pureStepsW φ (n + 1) line = pureAdvanceW φ (pureStepsW φ n line)
  | 0, _ => rfl
  | n + 1, line => pureStepsW_succ' φ n (pureAdvanceW φ line)

/-- After `current_step` steps the timeline has one row per step and its last
row is `pureStepsW` applied that many times to the seed. -/
def TimelineInv (cnf : Cnf) (m : SatMachinePureImproves) : Prop :=
  m.cnf = cnf ∧ m.timeline.length = m.current_step + 1 ∧
    m.timeline.getLast? = some (pureStepsW cnf m.current_step (pureInit cnf))

theorem init_pure_inv (cnf : Cnf) : TimelineInv cnf (init_pure cnf) :=
  ⟨rfl, rfl, rfl⟩

theorem step_pure_inv (cnf : Cnf) (m : SatMachinePureImproves) (hinv : TimelineInv cnf m)
    (h : m.current_step < (stepCount cnf).toNat - 1) :
    TimelineInv cnf (step_pure m) ∧ (step_pure m).current_step = m.current_step + 1 := by
  obtain ⟨hcnf, hlen, hlast⟩ := hinv
  subst hcnf
  have hlt : m.current_step < m.timeline.length := by omega
  have hget : m.timeline[m.current_step]! = pureStepsW m.cnf m.current_step (pureInit m.cnf) := by
    rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel] at hlast
    rw [List.getElem!_eq_getElem?_getD, hlast]
    rfl
  rw [step_pure_of_lt m h, if_pos hlt, hget]
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · simp [hlen]
  · rw [List.getLast?_concat, pureStepsW_succ']

theorem run_pure_fuel_inv (cnf : Cnf) : ∀ (fuel : Nat) (m : SatMachinePureImproves),
    TimelineInv cnf m →
    m.current_step ≤ (stepCount cnf).toNat - 1 →
    (stepCount cnf).toNat - 1 ≤ m.current_step + fuel →
    TimelineInv cnf (run_pure_fuel cnf fuel m) ∧
      (run_pure_fuel cnf fuel m).current_step = (stepCount cnf).toNat - 1
  | 0, m, hinv, hle, hfuel => by
    simp only [run_pure_fuel]
    exact ⟨hinv, by omega⟩
  | fuel + 1, m, hinv, hle, hfuel => by
    simp only [run_pure_fuel]
    by_cases hdone : m.current_step ≥ (stepCount cnf).toNat - 1
    · rw [if_pos hdone]
      exact ⟨hinv, by omega⟩
    · rw [if_neg hdone]
      obtain ⟨hinv', hcur⟩ := step_pure_inv cnf m hinv (by omega)
      exact run_pure_fuel_inv cnf fuel (step_pure m) hinv' (by omega) (by omega)

theorem run_pure_inv (cnf : Cnf) :
    TimelineInv cnf (run_pure cnf) ∧
      (run_pure cnf).current_step = (stepCount cnf).toNat - 1 :=
  run_pure_fuel_inv cnf (stepCount cnf).toNat (init_pure cnf) (init_pure_inv cnf)
    (by simp [init_pure]) (by simp [init_pure])

theorem run_pure_getLast? (cnf : Cnf) :
    (run_pure cnf).timeline.getLast? = some (pureRunW cnf) := by
  obtain ⟨⟨_, _, hlast⟩, hcur⟩ := run_pure_inv cnf
  have hsteps : (stepCount cnf - 1).toNat = (stepCount cnf).toNat - 1 := by omega
  rw [hlast, hcur, pureRunW, hsteps]

/-- **The bridge.** The improved machine's final row is exactly `pureRunW`. -/
theorem final_line_run_pure (cnf : Cnf) : final_line (run_pure cnf) = pureRunW cnf := by
  simp only [final_line, List.getLastD_eq_getLast?, run_pure_getLast?, Option.getD_some]

/-- The improved machine says SAT exactly when its driver ends with a non-empty line. -/
theorem is_satisfiable_run_pure_iff (cnf : Cnf) :
    is_satisfiable (run_pure cnf) = true ↔ pureRunW cnf ≠ [] := by
  simp only [is_satisfiable, final_line_run_pure, Bool.not_eq_true', List.isEmpty_eq_false_iff]

theorem solution_count_run_pure (cnf : Cnf) :
    solution_count (run_pure cnf) = (pureRunW cnf).length := by
  simp only [solution_count, final_line_run_pure]

/-- **Completeness of the improved machine.** A satisfiable well-formed formula
is reported SAT. No open hypothesis. -/
theorem completeness_improves (cnf : Cnf) (hwf : WF cnf) (h : Satisfiable cnf) :
    is_satisfiable (run_pure cnf) = true :=
  (is_satisfiable_run_pure_iff cnf).mpr (pureRunW_ne_nil cnf hwf h)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.SatMachine.PureProofsImproves.final_line_run_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms final_line_run_pure

/-- info: 'AbsSat.SatMachine.PureProofsImproves.completeness_improves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_improves

end AbsSat.SatMachine.PureProofsImproves
