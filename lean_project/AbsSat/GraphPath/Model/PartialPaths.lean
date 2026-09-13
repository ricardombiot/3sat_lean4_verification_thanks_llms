-- lean_project/AbsSat/GraphPath/Model/PartialPaths.lean
import AbsSat.GraphPath.Model.PrefixDecode

/-!
# Construction by partial paths: `Φ_k`

`docs/demostración_por_construcción.md` proposes reading the machine as building
partial paths step by step, with `Φ` at the last step the complete set of paths. This
module makes `Φ_k` a definition and packages the two inclusions the project already
proved:

* `Phi line p` — some state of the line represents the path `p` (`denot`);
* `assignPath_mem_Phi` — every assignment satisfying the clauses seen by step `k`
  leaves its path in `Φ_k` (from `pureSteps_carries_prefix`);
* `Phi_sound` — every path in `Φ_k` comes from a co-owned chain that decodes to an
  assignment satisfying those clauses (from `satUpTo_of_chain`);
* `satisfiable_iff_Phi_nonempty` — at the last step, **unconditionally**, the formula is
  satisfiable iff `Φ` is non-empty.

The construction is therefore sound and complete at the level of *represented paths*.
What the machine answers is different: whether the last line has states at all. The
gap is stated exactly in `soundness_iff_nonempty_represents`: the machine is correct
iff a non-empty last line always represents some complete path — which is what
`ClauseStepExact` is for.
-/

namespace AbsSat.GraphPath.Model.PartialPaths

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.CnfChain
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.Conservation
open AbsSat.GraphPath.Model.PrefixConservation
open AbsSat.GraphPath.Model.PrefixDecode

/-- The driver's line after `k` steps. -/
def lineAt (φ : Cnf) (k : Nat) : PureLine := pureSteps φ k (pureInit φ)

/-- `Φ` of a line: the paths some state of the line represents. -/
def Phi (line : PureLine) (p : List NodeId) : Prop := ∃ kv ∈ line, denot kv.2 p

/-- The path an assignment names through the first `n` steps of the map. -/
def assignPath (φ : Cnf) (a : Assign) (n : Int) : List NodeId :=
  (intRange 0 (n - 1)).reverse.map (selOfAssign φ a)

theorem lineAt_ok (φ : Cnf) (k : Nat) : LineOk φ k (lineAt φ k) := by
  have h := Decision.LineOk_pureSteps φ k 0 (pureInit φ) (Decision.LineOk_pureInit φ)
  unfold lineAt
  simpa using h

/-- **Every partial solution is in `Φ_k`.** -/
theorem assignPath_mem_Phi (φ : Cnf) (hwf : WF φ) (k : Nat) (hk : (k : Int) < stepCount φ)
    (a : Assign) (hs : SatUpTo φ a k) :
    Phi (lineAt φ k) (assignPath φ a ((k : Int) + 1)) := by
  obtain ⟨g, hmem, hcs, sel, hsound, hid⟩ := pureSteps_carries_prefix φ a hwf k hk hs
  have hc : ChainG g sel := hsound.chain
  obtain ⟨hchain, howned, _⟩ := hc
  refine ⟨(selOfAssign φ a k, g), hmem, sel, hchain, howned, ?_⟩
  simp only [assignPath, pathOf]
  rw [hcs]
  refine List.map_congr_left ?_
  intro x hx
  have hx' := List.mem_reverse.mp hx
  have h0 := mem_intRange_lower hx'
  have h1 := mem_intRange_upper hx'
  exact (hid x h0 (by rw [hcs]; omega)).symm

/-- **Every path in `Φ_k` is a partial solution.** -/
theorem Phi_sound (φ : Cnf) (hwf : WF φ) (k : Int) (line : PureLine) (hl : LineOk φ k line)
    (p : List NodeId) (hp : Phi line p) :
    ∃ kv ∈ line, ∃ sel, IsChain kv.2 sel ∧ PairwiseOwned kv.2 sel ∧ p = pathOf sel kv.2 ∧
      SatUpTo φ (decode sel) k := by
  obtain ⟨kv, hkv, sel, hchain, howned, hpeq⟩ := hp
  have hok := hl.2 kv hkv
  have hsat := satUpTo_of_chain φ hwf kv.2 hok.reach sel hchain howned
  have hk : kv.2.current_step - 1 = k := by rw [hok.step]; omega
  rw [hk] at hsat
  exact ⟨kv, hkv, sel, hchain, howned, hpeq, hsat⟩

theorem sat_of_satUpTo_final (φ : Cnf) (a : Assign) (hs : SatUpTo φ a (stepCount φ - 1)) :
    Sat a φ := by
  intro c hc
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hj
  exact hs j c hj (by simp only [clauseStep, stepCount]; omega)

/-- **`Φ` at the last step is exactly the solutions**, with no open hypothesis. -/
theorem satisfiable_iff_Phi_nonempty (φ : Cnf) (hwf : WF φ) :
    Satisfiable φ ↔ ∃ p, Phi (pureRun φ) p := by
  have hcount : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hrun : pureRun φ = lineAt φ (stepCount φ - 1).toNat := rfl
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨assignPath φ a (((stepCount φ - 1).toNat : Int) + 1), ?_⟩
    rw [hrun]
    exact assignPath_mem_Phi φ hwf _ (by omega) a (by rw [hcast]; exact satUpTo_of_sat φ a ha _)
  · rintro ⟨p, hp⟩
    rw [hrun] at hp
    obtain ⟨_, _, sel, _, _, _, hsat⟩ := Phi_sound φ hwf _ _ (lineAt_ok φ _) p hp
    rw [hcast] at hsat
    exact ⟨decode sel, sat_of_satUpTo_final φ _ hsat⟩

/-- **The open part, stated exactly.** A non-empty last line implies satisfiability iff
a non-empty last line always represents some complete path. -/
theorem soundness_iff_nonempty_represents (φ : Cnf) (hwf : WF φ) :
    (pureRun φ ≠ [] → Satisfiable φ) ↔ (pureRun φ ≠ [] → ∃ p, Phi (pureRun φ) p) := by
  rw [satisfiable_iff_Phi_nonempty φ hwf]

/-- info: 'AbsSat.GraphPath.Model.PartialPaths.assignPath_mem_Phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms assignPath_mem_Phi

/-- info: 'AbsSat.GraphPath.Model.PartialPaths.Phi_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Phi_sound

/-- info: 'AbsSat.GraphPath.Model.PartialPaths.satisfiable_iff_Phi_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms satisfiable_iff_Phi_nonempty

/-- info: 'AbsSat.GraphPath.Model.PartialPaths.soundness_iff_nonempty_represents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundness_iff_nonempty_represents

end AbsSat.GraphPath.Model.PartialPaths
