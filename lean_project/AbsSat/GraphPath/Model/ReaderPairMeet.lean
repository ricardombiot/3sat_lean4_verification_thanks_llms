-- lean_project/AbsSat/GraphPath/Model/ReaderPairMeet.lean
import AbsSat.GraphPath.Model.PinExtends
import AbsSat.GraphPath.Model.Descent

/-!
# The reader never gets stuck, under the pairwise hypothesis

`NoDeadEndVerdict.sat_of_pairMeet` gets `Satisfiable φ` out of `PairMeet` + `TwoParents` on the
**final** state. That is a fact about the formula, not about what the machine prints: nothing outside
`ReaderExec` concludes `readerVerdictW φ = true`, so until now the strongest measured hypothesis of
the repo still allowed the machine to answer `unknown`.

This module closes that gap. The same two hypotheses, asked along the **reader's trajectory**, give
`PinExtends`, and with it everything `PinExtends.lean` already proves:

* **`chain_of_pairMeet`** — one valid reader state with `PairMeet` and `TwoParents` holds a chain.
  It is `commonOwner_of_pairMeet` → `noDeadEnd_of_commonOwner` → `topAnchor_of` →
  `nonempty_of_noDeadEnd`, at a state of the reader rather than at the final state.
* **`twoParents_of_pruned`** — `TwoParents` **descends along pruning**, so it only has to hold at the
  state the reader starts from: every state it reaches is a `Pruned` of it and inherits it. Only
  `PairMeet` is a hypothesis on the whole trajectory.
* **`pinExtends_of_pairMeet`** — the pin the reader needs is the chain's own node at that step.
* **`answer_ne_unknown_pm`** / **`answer_unsat_pm`** — *the machine never answers `unknown`*, and on
  an unsatisfiable formula it answers `unsat`.

What is left to measure is therefore exactly `RunPairMeet`: `PairMeet` after every pin, not just on
the final state (which is where the six sweeps of v166 measured it, 753 nodes, 0 counterexamples).
-/

namespace AbsSat.GraphPath.Model.ReaderPairMeet

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.PinExtends
open AbsSat.GraphPath.Model.Answer (Answer answer)

-- ============================================================
-- `TwoParents` descends along pruning
-- ============================================================

/-- **A narrowing keeps at most two parents.** `Pruned` derives every node from one of the wider
state with its parent list contained, so three parents of a node here are three parents of a node
there. Every state the reader reaches is a `Pruned` of the one it started from (`rf_readFrom`), so
`TwoParents` only has to be checked once, at the seed. -/
theorem twoParents_of_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : Descent.TwoParents g) : Descent.TwoParents g' := by
  intro n' hn' c hc c' hc' c'' hc''
  obtain ⟨n, hn, _, _, hpar⟩ := hpr.nodes_derived n' hn'
  exact h n hn c (hpar c hc) c' (hpar c' hc') c'' (hpar c'' hc'')

-- ============================================================
-- A chain at one state of the reader
-- ============================================================

/-- **One reader state with the pairwise hypothesis holds a chain.** The top anchor is free
(`topAnchor_of`), `PairMeet` and `TwoParents` give the one-step descent (`commonOwner_of_pairMeet`,
`noDeadEnd_of_commonOwner`), and a descent that reaches step 0 is a `ChainSound` chain. -/
theorem chain_of_pairMeet (S : GPathM) (h : RF S) (hv : isValid S = true)
    (hpos : 0 < S.current_step)
    (htp : Descent.TwoParents S) (hpm : Descent.PairMeet S) : ∃ sel, ChainSound S sel := by
  have a := adj_rf h hv
  have hok := aggOk_rf h hv
  have hnd := Descent.noDeadEnd_of_commonOwner S a hok
    (Descent.commonOwner_of_pairMeet S a hok htp hpm)
  have ha := NoDeadEnd.topAnchor_of S hv hpos a.rc.gn a.rc.oos a.rc.shape a.rc.rootz
    (fun q d hd => a.ctx.nodeval q d hd)
  obtain ⟨_, sel, hsc, _⟩ := NoDeadEnd.nonempty_of_noDeadEnd S hpos ha hnd
  exact ⟨sel, hsc⟩

-- ============================================================
-- The hypothesis of `PinExtends`, discharged
-- ============================================================

/-- **The pin the reader needs is the chain's own node.** Pinning the map node the chain selects at
step `l` keeps the chain (`ChainSound_filterAllAgg`), and a chain makes the state valid
(`isValid_of_ChainG`) — so `PairMeet` along the trajectory, plus `TwoParents` at the seed, discharge
`PinExtends`. -/
theorem pinExtends_of_pairMeet (g₀ : GPathM) (h0 : RF g₀) (hpos : 0 < g₀.current_step)
    (htp : Descent.TwoParents g₀)
    (hpm : ∀ S, ReadFrom g₀ S → isValid S = true → Descent.PairMeet S) :
    PinExtends g₀ := by
  intro S hS hv l hl0 hl1
  obtain ⟨hrf, hpr⟩ := rf_readFrom h0 hS
  obtain ⟨sel, hsc⟩ := chain_of_pairMeet S hrf hv (by rw [hpr.step_eq]; exact hpos)
    (twoParents_of_pruned hpr htp) (hpm S hS hv)
  obtain ⟨_, hstep⟩ := hsc.chain.1.1 l hl0 hl1
  refine ⟨(sel l).id, hstep, ?_⟩
  refine PickInduction.isValid_of_ChainG _ sel
    (ChainSound_filterAllAgg S [(sel l).id] sel hsc ?_).chain
  intro req hreq _ _
  rw [List.mem_singleton.mp hreq, hstep]

-- ============================================================
-- The run, and the machine's output
-- ============================================================

variable (φ : Cnf)

/-- **The hypothesis to measure**: `PairMeet` at every state the reader reaches from every state of
the final line — the final state, and every state a pin leaves behind. -/
def RunPairMeet : Prop :=
  ∀ kv ∈ pureRunW φ, ∀ S, ReadFrom (filterAllAgg kv.2 []) S → isValid S = true →
    Descent.PairMeet S

/-- **The in-degree side, only at the seed**: `twoParents_of_pruned` carries it down the trajectory. -/
def RunTwoParents : Prop :=
  ∀ kv ∈ pureRunW φ, Descent.TwoParents (filterAllAgg kv.2 [])

theorem pos_final (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) :
    0 < (filterAllAgg kv.2 []).current_step := by
  obtain ⟨_, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  rw [(pruned_filterAllAgg kv.2 []).step_eq, hstep]
  exact ConservationCore.stepCount_pos φ

/-- **The pairwise hypothesis gives the reader's.** -/
theorem runPinExtends_of_pairMeet (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ) :
    RunPinExtends φ := fun kv hkv =>
  pinExtends_of_pairMeet _ (rf_final φ hwf kv hkv) (pos_final φ hwf kv hkv) (htp kv hkv)
    (hpm kv hkv)

/-- **The verdict under the pairwise hypothesis.** -/
theorem sat_of_pairMeetRun (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_pinExtends φ hwf (runPinExtends_of_pairMeet φ hwf htp hpm) kv hkv hv

/-- **The machine decides, under the pairwise hypothesis.** -/
theorem verdict_iff_pairMeet (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  verdict_iff_pinExtends φ hwf (runPinExtends_of_pairMeet φ hwf htp hpm)

/-- **The reader never gets stuck**, under `PairMeet` along its trajectory and `TwoParents` at the
seed: the machine never answers `unknown`. This is what `sat_of_pairMeet` did *not* give — it proved
the formula satisfiable, not that the machine says so. -/
theorem answer_ne_unknown_pm (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ) :
    answer φ ≠ .unknown :=
  answer_ne_unknown_px φ hwf (runPinExtends_of_pairMeet φ hwf htp hpm)

/-- **And on an unsatisfiable formula it answers `unsat`.** -/
theorem answer_unsat_pm (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ)
    (hns : ¬ Satisfiable φ) : answer φ = .unsat :=
  answer_unsat_px φ hwf (runPinExtends_of_pairMeet φ hwf htp hpm) hns

/-- info: 'AbsSat.GraphPath.Model.ReaderPairMeet.twoParents_of_pruned' does not depend on any axioms -/
#guard_msgs in
#print axioms twoParents_of_pruned

/-- info: 'AbsSat.GraphPath.Model.ReaderPairMeet.chain_of_pairMeet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_of_pairMeet

/-- info: 'AbsSat.GraphPath.Model.ReaderPairMeet.pinExtends_of_pairMeet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinExtends_of_pairMeet

/-- info: 'AbsSat.GraphPath.Model.ReaderPairMeet.answer_ne_unknown_pm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_pm

/-- info: 'AbsSat.GraphPath.Model.ReaderPairMeet.answer_unsat_pm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_pm

end AbsSat.GraphPath.Model.ReaderPairMeet
