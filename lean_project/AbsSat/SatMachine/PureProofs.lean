import AbsSat.SatMachine.PureSatMachine

/-!
# Bridge: `SatMachinePure` ↔ `PureDriver`

Theorem 01 of `docs/theorems/`: the last row of the pure machine's timeline is
exactly `PureDriver.pureRun`, so every result proven about `pureRun` applies
to `run_pure`.
-/

namespace AbsSat.SatMachine.PureProofs

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.SatMachine.PureSatMachine

theorem init_pure_timeline (cnf : Cnf) :
    (init_pure cnf).timeline = [pureInit cnf] := rfl

theorem step_pure_of_lt (m : SatMachinePure)
    (h : m.current_step < (stepCount m.cnf).toNat - 1) :
    step_pure m =
      { cnf := m.cnf
        timeline := m.timeline ++ [pureAdvance m.cnf
          (if m.current_step < m.timeline.length then m.timeline[m.current_step]! else [])]
        current_step := m.current_step + 1 } := by
  simp only [step_pure]
  rw [if_neg (show ¬ m.current_step ≥ (stepCount m.cnf).toNat - 1 by omega)]

theorem step_pure_timeline (m : SatMachinePure)
    (h : m.current_step < (stepCount m.cnf).toNat - 1) :
    (step_pure m).timeline =
      m.timeline ++ [pureAdvance m.cnf
        (if m.current_step < m.timeline.length then m.timeline[m.current_step]! else [])] := by
  rw [step_pure_of_lt m h]

theorem pureSteps_succ' (φ : Cnf) : ∀ (n : Nat) (line : PureLine),
    pureSteps φ (n + 1) line = pureAdvance φ (pureSteps φ n line)
  | 0, _ => rfl
  | n + 1, line => pureSteps_succ' φ n (pureAdvance φ line)

/-- After `current_step` steps the timeline has one row per step and its last
row is `pureSteps` applied that many times to the seed. -/
def TimelineInv (cnf : Cnf) (m : SatMachinePure) : Prop :=
  m.cnf = cnf ∧ m.timeline.length = m.current_step + 1 ∧
    m.timeline.getLast? = some (pureSteps cnf m.current_step (pureInit cnf))

theorem init_pure_inv (cnf : Cnf) : TimelineInv cnf (init_pure cnf) :=
  ⟨rfl, rfl, rfl⟩

theorem step_pure_inv (cnf : Cnf) (m : SatMachinePure) (hinv : TimelineInv cnf m)
    (h : m.current_step < (stepCount cnf).toNat - 1) :
    TimelineInv cnf (step_pure m) ∧ (step_pure m).current_step = m.current_step + 1 := by
  obtain ⟨hcnf, hlen, hlast⟩ := hinv
  subst hcnf
  have hlt : m.current_step < m.timeline.length := by omega
  have hget : m.timeline[m.current_step]! = pureSteps m.cnf m.current_step (pureInit m.cnf) := by
    rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel] at hlast
    rw [List.getElem!_eq_getElem?_getD, hlast]
    rfl
  rw [step_pure_of_lt m h, if_pos hlt, hget]
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · simp [hlen]
  · rw [List.getLast?_concat, pureSteps_succ']

theorem run_pure_fuel_inv (cnf : Cnf) : ∀ (fuel : Nat) (m : SatMachinePure),
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
    (run_pure cnf).timeline.getLast? = some (pureRun cnf) := by
  obtain ⟨⟨_, _, hlast⟩, hcur⟩ := run_pure_inv cnf
  have hsteps : (stepCount cnf - 1).toNat = (stepCount cnf).toNat - 1 := by omega
  rw [hlast, hcur, pureRun, hsteps]

/-- Theorem 01: the pure machine's final row is exactly `PureDriver.pureRun`. -/
theorem run_pure_eq_driver (cnf : Cnf) :
    (run_pure cnf).timeline.getLast! = pureRun cnf := by
  rw [List.getLast!_eq_getLast?_getD, run_pure_getLast?]
  rfl

end AbsSat.SatMachine.PureProofs
