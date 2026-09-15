import AbsSat.GraphPath.Model.UnitPropReview
import AbsSat.Cnf.HornModel
import AbsSat.SatMachine.PureProofs

/-!
# Horn formulas: the machine decides them

The last advance of the driver sends every state of the last clause step to the fusion top. At that
point every clause has been processed, and the fusion top pins nothing. So if unit propagation over
all the clauses reaches a conflict, `UnitPropReview.conflict_invalid` makes every one of those sends
invalid, and the run ends empty.

* `pureRun_nil_of_conflict` — a unit-propagation conflict over the clauses empties the last line
  (any well-formed formula, Horn or not);
* `unsat_of_conflict` — so the machine answers UNSAT;
* `horn_decides` — for a well-formed Horn formula, the machine's answer is exactly satisfiability:
  SAT means no conflict (above), and no conflict means a model (`Cnf.horn_satisfiable_iff`); the
  other direction is `completeness_pure`.
-/

namespace AbsSat.GraphPath.Model.HornDecision

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.Decision
open AbsSat.GraphPath.Model.UnitPropReview
open AbsSat.SatMachine.PureSatMachine
open AbsSat.SatMachine.PureProofs

variable (φ : Cnf)

/-- At the fusion top every clause has been processed. -/
theorem clauses_processed (g : GPathM) (hg : g.current_step = fusionTop φ) :
    ∀ c ∈ φ.clauses, c ∈ processed φ g := by
  intro c hc
  obtain ⟨j, hj, hget⟩ := exists_index_of_mem φ.clauses c hc
  have hlt : clauseStep φ j < g.current_step := by
    rw [hg]
    simp only [clauseStep, fusionTop]
    omega
  exact List.mem_filterMap.mpr ⟨j, List.mem_range.mpr hj, by rw [if_pos hlt]; exact hget⟩

/-- **A send into the fusion top is dropped** when the clauses have a conflict. -/
theorem sendTo_last (hwf : WF φ) (hc : Conflict φ.clauses []) (kv : NodeId × GPathM)
    (hkv : StateOk φ (fusionTop φ - 1) kv) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index) (next : PureLine) :
    sendTo φ kv.2 next d = next := by
  have hkey : kv.1.step = fusionTop φ - 1 := mapNodes_step φ _ kv.1 hkv.onMap
  have hmk : (⟨fusionTop φ - 1, kv.1.index⟩ : NodeId) ∈ mapNodes φ (fusionTop φ - 1) := by
    have e : (⟨fusionTop φ - 1, kv.1.index⟩ : NodeId) = kv.1 := by rw [← hkey]
    rw [e]
    exact hkv.onMap
  have hd' : d ∈ mapNodes φ (fusionTop φ - 1 + 1) :=
    mapSons_subset φ _ kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = fusionTop φ - 1 + 1 := mapNodes_step φ _ d hd'
  have hcur : kv.2.current_step = fusionTop φ := by rw [hkv.step]; omega
  have hdm : d ∈ mapNodes φ d.step := by rw [hdstep]; exact hd'
  have hcd : d.step = kv.2.current_step := by rw [hdstep, hcur]; omega
  have hinv := conflict_invalid φ hwf kv.2 hkv.reach d hcd hdm
    (conflict_mono (clauses_processed φ kv.2 hcur) (fun _ h => absurd h List.not_mem_nil) hc)
  have hup : upFiltering kv.2 (reqOfCnf φ d) d "" = filterAll kv.2 (reqOfCnf φ d) := by
    unfold upFiltering GPathM.up
    rw [if_neg (by rw [hinv]; decide)]
  unfold sendTo
  rw [if_neg (by rw [hup, hinv]; decide)]

theorem sendAll_last (hwf : WF φ) (hc : Conflict φ.clauses []) (kv : NodeId × GPathM)
    (hkv : StateOk φ (fusionTop φ - 1) kv) (next : PureLine) : sendAll φ kv next = next := by
  unfold sendAll
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, l.foldl (sendTo φ kv.2) acc = acc := by
    intro l
    induction l with
    | nil => intro _ acc; rfl
    | cons x xs ih =>
      intro hx acc
      rw [List.foldl_cons, sendTo_last φ hwf hc kv hkv x (hx x List.mem_cons_self) acc]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) acc
  exact main _ (fun _ hd => hd) next

/-- **The last advance empties the line** when the clauses have a conflict. -/
theorem pureAdvance_last (hwf : WF φ) (hc : Conflict φ.clauses []) (line : PureLine)
    (hl : LineOk φ (fusionTop φ - 1) line) : pureAdvance φ line = [] := by
  unfold pureAdvance
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOk φ (fusionTop φ - 1) kv) →
      ∀ acc, l.foldl (fun next kv => sendAll φ kv next) acc = acc := by
    intro l
    induction l with
    | nil => intro _ acc; rfl
    | cons x xs ih =>
      intro hx acc
      rw [List.foldl_cons, sendAll_last φ hwf hc x (hx x List.mem_cons_self) acc]
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) acc
  exact main line hl.2 []

/-- **A unit-propagation conflict over the clauses empties the run.** -/
theorem pureRun_nil_of_conflict (hwf : WF φ) (hc : Conflict φ.clauses []) : pureRun φ = [] := by
  have hn : (stepCount φ - 1).toNat = (fusionTop φ - 1).toNat + 1 := by
    simp only [stepCount, fusionTop]
    omega
  unfold pureRun
  rw [hn, pureSteps_succ' φ]
  refine pureAdvance_last φ hwf hc _ ?_
  have h := LineOk_pureSteps φ (fusionTop φ - 1).toNat 0 (pureInit φ) (LineOk_pureInit φ)
  have hcast : (0 : Int) + (((fusionTop φ - 1).toNat : Nat) : Int) = fusionTop φ - 1 := by
    simp only [fusionTop]
    omega
  rw [hcast] at h
  exact h

/-- **The machine answers UNSAT** when unit propagation over the clauses reaches a conflict. -/
theorem unsat_of_conflict (hwf : WF φ) (hc : Conflict φ.clauses []) :
    is_satisfiable (run_pure φ) = false := by
  cases h : is_satisfiable (run_pure φ) with
  | false => rfl
  | true => exact absurd (pureRun_nil_of_conflict φ hwf hc) ((is_satisfiable_run_pure_iff φ).mp h)

/-- **The machine decides well-formed Horn formulas.** -/
theorem horn_decides (hwf : WF φ) (hh : φ.Horn) :
    is_satisfiable (run_pure φ) = true ↔ Satisfiable φ :=
  ⟨fun h => (Cnf.horn_satisfiable_iff φ hh).mpr
      (fun hc => (is_satisfiable_run_pure_iff φ).mp h (pureRun_nil_of_conflict φ hwf hc)),
    completeness_pure φ hwf⟩

/-- info: 'AbsSat.GraphPath.Model.HornDecision.pureRun_nil_of_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRun_nil_of_conflict

/-- info: 'AbsSat.GraphPath.Model.HornDecision.unsat_of_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unsat_of_conflict

/-- info: 'AbsSat.GraphPath.Model.HornDecision.horn_decides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms horn_decides

end AbsSat.GraphPath.Model.HornDecision
