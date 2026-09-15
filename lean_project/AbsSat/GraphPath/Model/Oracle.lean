-- lean_project/AbsSat/GraphPath/Model/Oracle.lean
import AbsSat.GraphPath.Model.PartialPaths
import AbsSat.GraphPath.Model.EmptinessReduction
import AbsSat.Cnf.BruteForce

/-!
# The machine against the brute-force oracle

`Cnf.BruteForce` enumerates the `2^nVars` Boolean lists and keeps those that satisfy the formula
(`bruteForceSat_sound`, `bruteForceSat_complete`). This module compares that oracle with what the
machine builds, following `docs/demostración_por_equivalencia.md`.

**What the machine represents is exactly the oracle's set** (up to the choice of path for an
assignment and the values of variables beyond `nVars`):

* `Phi_to_oracle` — every path the last line represents comes from a co-owned chain whose decoded
  assignment, restricted to the formula's variables, is in `bruteForceSat φ`;
* `oracle_to_Phi` — every list the oracle returns names a path the last line represents;
* `Phi_nonempty_iff_oracle` — the represented set is non-empty iff the oracle's list is.

**What the machine answers** is whether its last line has states. Against the oracle:

* `oracle_nonempty_run_pure` — if the oracle finds a solution, the machine answers SAT
  (unconditionally; this is completeness);
* `run_pure_iff_oracle_of_SendExact` — under `SendExact` the machine's answer is the oracle's;
* `answer_matches_oracle_iff` — the machine's SAT answer always agrees with the oracle **iff** a
  non-empty last line always represents some path. That is the emptiness test of the graph
  representation, and it is the only open part of the comparison.
-/

namespace AbsSat.GraphPath.Model.Oracle

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.PartialPaths
open AbsSat.GraphPath.Model.PrefixConservation
open AbsSat.GraphPath.Model.CnfChain
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.SatMachine.PureSatMachine

/-- The Boolean list an assignment gives the oracle: its first `nVars` values. -/
def restrict (φ : Cnf) (a : Assign) : List Bool := (List.range φ.nVars).map a

/-- A satisfying assignment, restricted to the formula's variables, is in the oracle's list. -/
theorem restrict_mem_bruteForceSat (φ : Cnf) (hwf : WF φ) (a : Assign) (ha : Sat a φ) :
    restrict φ a ∈ bruteForceSat φ := by
  simp only [bruteForceSat, List.mem_filter]
  refine ⟨enum_complete _ a, ?_⟩
  exact (satB_iff _ φ).mpr
    (sat_congr_below φ hwf a _ (fun i hi => (toAssign_map_range _ a i hi).symm) ha)

/-- **Every represented path is an oracle solution.** -/
theorem Phi_to_oracle (φ : Cnf) (hwf : WF φ) (p : List NodeId) (hp : Phi (pureRun φ) p) :
    ∃ sel, (∃ kv ∈ pureRun φ, IsChain kv.2 sel ∧ PairwiseOwned kv.2 sel ∧ p = pathOf sel kv.2) ∧
      restrict φ (decode sel) ∈ bruteForceSat φ := by
  have hcount : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hrun : pureRun φ = lineAt φ (stepCount φ - 1).toNat := rfl
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  rw [hrun] at hp
  obtain ⟨kv, hkv, sel, hchain, howned, hpeq, hsat⟩ := Phi_sound φ hwf _ _ (lineAt_ok φ _) p hp
  rw [hcast] at hsat
  exact ⟨sel, ⟨kv, by rw [hrun]; exact hkv, hchain, howned, hpeq⟩,
    restrict_mem_bruteForceSat φ hwf _ (sat_of_satUpTo_final φ _ hsat)⟩

/-- **Every oracle solution is represented.** -/
theorem oracle_to_Phi (φ : Cnf) (hwf : WF φ) (l : List Bool) (hl : l ∈ bruteForceSat φ) :
    Phi (pureRun φ) (assignPath φ (toAssign l) (stepCount φ)) := by
  have hcount : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hrun : pureRun φ = lineAt φ (stepCount φ - 1).toNat := rfl
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  have hmem := assignPath_mem_Phi φ hwf (stepCount φ - 1).toNat (by omega) (toAssign l)
    (by rw [hcast]; exact satUpTo_of_sat φ _ (bruteForceSat_sound φ l hl) _)
  have hk : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by omega
  rw [hk] at hmem
  rw [hrun]
  exact hmem

/-- **The represented set is non-empty exactly when the oracle's list is.** -/
theorem Phi_nonempty_iff_oracle (φ : Cnf) (hwf : WF φ) :
    (∃ p, Phi (pureRun φ) p) ↔ bruteForceSat φ ≠ [] := by
  rw [bruteForceSat_ne_nil_iff φ hwf]
  exact (satisfiable_iff_Phi_nonempty φ hwf).symm

/-- **If the oracle finds a solution, the machine answers SAT.** -/
theorem oracle_nonempty_run_pure (φ : Cnf) (hwf : WF φ) :
    bruteForceSat φ ≠ [] → is_satisfiable (run_pure φ) = true :=
  fun h => AbsSat.SatMachine.PureProofs.completeness_pure φ hwf ((bruteForceSat_ne_nil_iff φ hwf).mp h)

/-- **Under `SendExact`, the machine's answer is the oracle's.** -/
theorem run_pure_iff_oracle_of_SendExact (φ : Cnf) (hwf : WF φ)
    (hex : EmptinessReduction.SendExact φ) :
    is_satisfiable (run_pure φ) = true ↔ bruteForceSat φ ≠ [] := by
  rw [bruteForceSat_ne_nil_iff φ hwf]
  exact EmptinessReduction.run_pure_decides_of_SendExact φ hwf hex

/-- **The open part of the comparison, stated exactly.** The machine's SAT answer always agrees
with the oracle iff a non-empty last line always represents some path. -/
theorem answer_matches_oracle_iff (φ : Cnf) (hwf : WF φ) :
    (is_satisfiable (run_pure φ) = true → bruteForceSat φ ≠ []) ↔
      (pureRun φ ≠ [] → ∃ p, Phi (pureRun φ) p) := by
  rw [bruteForceSat_ne_nil_iff φ hwf, AbsSat.SatMachine.PureProofs.is_satisfiable_run_pure_iff φ]
  exact soundness_iff_nonempty_represents φ hwf

/-- info: 'AbsSat.GraphPath.Model.Oracle.Phi_to_oracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Phi_to_oracle

/-- info: 'AbsSat.GraphPath.Model.Oracle.oracle_to_Phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms oracle_to_Phi

/-- info: 'AbsSat.GraphPath.Model.Oracle.oracle_nonempty_run_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms oracle_nonempty_run_pure

/-- info: 'AbsSat.GraphPath.Model.Oracle.run_pure_iff_oracle_of_SendExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_pure_iff_oracle_of_SendExact

/-- info: 'AbsSat.GraphPath.Model.Oracle.answer_matches_oracle_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_matches_oracle_iff

end AbsSat.GraphPath.Model.Oracle
