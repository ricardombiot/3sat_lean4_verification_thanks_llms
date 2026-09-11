-- lean_project/AbsSat/GraphPath/Model/Decision.lean
import AbsSat.GraphPath.Model.NodeInvariant
import AbsSat.GraphPath.Model.L7
import AbsSat.GraphPath.Model.PureDriver

/-!
# The machine as a decision procedure, modulo the clause filter

Everything in the argument is now a theorem except `ClauseStepExact`. This
module assembles the consequence: **if the clause filter is exact, the machine
decides 3SAT** — a formula is satisfiable exactly when the run ends holding a
valid state.

* `→` is the driver theorem, `pureRun_full_state`, and needs nothing.
* `←` is `NodeInv_of_ClauseStepExact`: every node of the final state lies on a
  sound chain, so the state is inhabited, and `L7.sat_of_inhabited` decodes the
  chain into a satisfying assignment.

Since the run is polynomial in the formula, this also says precisely what
`ClauseStepExact` is worth: holding for every formula, it would put 3SAT in P.
-/

namespace AbsSat.GraphPath.Model.Decision

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.NodeInvariant

theorem LineOk_pureInit (φ : Cnf) : LineOk φ 0 (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineOk φ 0 acc →
        LineOk φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (LineOk_insertPure φ 0 acc x _ h (stateOk_initSeed φ x (hx x List.mem_cons_self)))
  exact main _ (fun _ hd => hd) [] ⟨by simp, fun kv hkv => absurd hkv List.not_mem_nil⟩

theorem LineOk_pureSteps (φ : Cnf) :
    ∀ (n : Nat) (k : Int) (line : PureLine), LineOk φ k line →
      LineOk φ (k + (n : Int)) (pureSteps φ n line) := by
  intro n
  induction n with
  | zero =>
    intro k line h
    have hk : k + ((0 : Nat) : Int) = k := by omega
    rw [hk]; exact h
  | succ m ih =>
    intro k line h
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureSteps]
    exact ih (k + 1) _ (LineOk_pureAdvance φ k line h)

/-- Every state of the last line is a full-length machine state. -/
theorem stateOk_pureRun (φ : Cnf) (hzero : (0 : Int) < stepCount φ) :
    ∀ kv ∈ pureRun φ, StateOk φ (stepCount φ - 1) kv := by
  have h := LineOk_pureSteps φ (stepCount φ - 1).toNat 0 (pureInit φ) (LineOk_pureInit φ)
  have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  rw [hcast] at h
  exact h.2

/-- **The machine decides 3SAT, if the clause filter is exact.** -/
theorem decides_of_ClauseStepExact (φ : Cnf) (hwf : WF φ) (hzero : (0 : Int) < stepCount φ)
    (h : ClauseStepExact φ) :
    Satisfiable φ ↔ ∃ kv ∈ pureRun φ, isValid kv.2 = true := by
  constructor
  · rintro ⟨a, hsat⟩
    obtain ⟨g, hmem, _, hv, _⟩ := pureRun_full_state φ a hwf hsat hzero
    exact ⟨_, hmem, hv⟩
  · rintro ⟨kv, hmem, hv⟩
    have hok := stateOk_pureRun φ hzero kv hmem
    have hreach : Reachable (reqOfCnf φ) kv.2 :=
      MapReachable.reachable_of_mapReachable φ hwf kv.2 hok.reach
    have hsup := NodeInv_of_ClauseStepExact φ h kv.2 hreach hv
    obtain ⟨sel, hsel⟩ := chain_of_SupportedS kv.2
      (GownersNodes.GN_reachable (reqOfCnf φ) kv.2 hreach) hsup hv
      (pos_reachable (reqOfCnf φ) kv.2 hreach)
    exact L7.satisfiable_of_inhabited φ hwf kv.2 hok.reach (by rw [hok.step]; omega)
      (Certifies.Inhabited_of_ChainSound kv.2 sel hsel)

/-- info: 'AbsSat.GraphPath.Model.Decision.decides_of_ClauseStepExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decides_of_ClauseStepExact

end AbsSat.GraphPath.Model.Decision
