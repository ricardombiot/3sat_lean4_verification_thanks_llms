-- lean_project/AbsSat/GraphPath/Model/ConservationImproves.lean
import AbsSat.GraphPath.Model.ConservationCore
import AbsSat.GraphPath.Model.ConservationFilter

/-!
# Conservation for the improved machine: the weak filter and the aggressive review never lose a solution

`Conservation` proves that `SatMachinePure` keeps every solution: along a
satisfying assignment's branch, the selection the assignment names stays a
sound chain of every state, and a chain inside the global owners makes the state
valid. `PureDriver` turns that into `pureRun_ne_nil`.

This module does the same for `PureDriverImproves`. The only new ingredient is
the weak filter, and it costs one lemma:

* `ChainSound_filterWeak` — `filterWeak` rewrites `gowners` only, so a sound
  chain survives it as soon as the chain's node at the entry's step is one of
  the entry's nodes;
* `weakReqOfCnf_sound` (in `CnfMapImproves`) — for a satisfying assignment it
  always is.

After the weak filter the state is a `Pruned` narrowing of the original, and
everything else is `Conservation`'s argument verbatim, run on the narrowed state.

## What changes in the bookkeeping

`AlongAssign` and `StateOk` carry `MapReachable`, whose `up` constructor is the
hard-requirement step: a weakly filtered state is not `MapReachable`. The only
things the conservation argument reads from reachability are that nodes lie
below the current step and `MachineOk`; both survive any pruning, `addNode`
and `join`. So here they are packaged as `ShapeOk`, and `AlongAssignW` /
`StateOkW` carry that instead.

## The review

The improved machine reviews with `AggressiveReview.reviewAgg`: the base review plus the author's
`agressive_consistence_filter!`, which drops owner pairs no path can contain together.
`ConservationFilter` is stated for any review with `ReviewOk` (it only removes, and it keeps every
sound chain), and `reviewAgg` has that instance, so the law below is the generic one with that
review.

## Result

`pureRunW_ne_nil`: for a well-formed satisfiable formula the improved run ends
with a non-empty line, and `pureRunW_full_state` gives the valid, inhabited
state parked at the assignment's final node. Unlike `PureDriver`, no
`0 < stepCount φ` hypothesis is needed: it always holds.
-/

namespace AbsSat.GraphPath.Model.ConservationImproves

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakReqOfCnf_sound)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit mem_insertPure
  mem_insertPure_of_ne key_inj isValid_of_grown insertPure_keys_some insertPure_keys_none
  isValid_initSeed)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.AggressiveReview (reviewAgg)
open AbsSat.GraphPath.Model.ConservationCore
open AbsSat.GraphPath.Model.ConservationFilter

-- ============================================================
-- The branch of an assignment, through the improved machine
-- ============================================================

variable (φ : Cnf) (a : Assign)

/-- `Conservation.AlongAssign` with the improved `up`, and `ShapeOk` in place of
`MapReachable` for the branch a join brings in. -/
inductive AlongAssignW : GPathM → Prop where
  | seed (title : String) :
      AlongAssignW (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String) :
      AlongAssignW g →
      AlongAssignW (upFilteringWeak g
        (weakReqOfCnf φ (selOfAssign φ a g.current_step))
        (reqOfCnf φ (selOfAssign φ a g.current_step))
        (selOfAssign φ a g.current_step) title)
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : ShapeOk g₂) :
      AlongAssignW g₁ → AlongAssignW (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : ShapeOk g₁) :
      AlongAssignW g₂ → AlongAssignW (GPathM.join g₁ g₂)

theorem shapeOk_of_alongW (g : GPathM) (h : AlongAssignW φ a g) : ShapeOk g := by
  induction h with
  | seed title => exact ShapeOk_initSeed _ title (selOfAssign_step φ a 0)
  | up g title _ ih =>
    exact ShapeOk_upFilteringWeak g _ _ _ title (selOfAssign_step φ a g.current_step) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact ShapeOk_join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact ShapeOk_join g₁ g₂ hok h₁ ih

-- ============================================================
-- The weak machine is the generic one, with no conditioned pass
-- ============================================================

/-- `filterACn 0` is the identity, so `Fsac φ 0` *is* the weak filter — the same term, not merely
an equal one. Everything `ConservationFilter` proves generically therefore applies here, and the
bookkeeping this module used to carry is gone. -/
theorem upFilteringF_eq (g : GPathM) (d : NodeId) (title : String) :
    upFilteringF φ (Fsac φ 0) reviewAgg g d title
      = upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d title := rfl

theorem sendTo_eq (g : GPathM) (next : PureLine) (d : NodeId) :
    sendToF φ (Fsac φ 0) reviewAgg g next d = sendToW φ g next d := rfl

theorem sendAll_eq (kv : NodeId × GPathM) (next : PureLine) :
    sendAllF φ (Fsac φ 0) reviewAgg kv next = sendAllW φ kv next := by
  unfold sendAllF sendAllW
  have h : sendToF φ (Fsac φ 0) reviewAgg kv.2 = sendToW φ kv.2 := by
    funext n d
    exact sendTo_eq φ kv.2 n d
  rw [h]

theorem advance_eq (line : PureLine) : pureAdvanceF φ (Fsac φ 0) reviewAgg line = pureAdvanceW φ line := by
  unfold pureAdvanceF pureAdvanceW
  have h : (fun next kv => sendAllF φ (Fsac φ 0) reviewAgg kv next) = (fun next kv => sendAllW φ kv next) := by
    funext next kv
    exact sendAll_eq φ kv next
  rw [h]

theorem steps_eq : ∀ (n : Nat) (line : PureLine),
    pureStepsF φ (Fsac φ 0) reviewAgg n line = pureStepsW φ n line
  | 0, _ => rfl
  | n + 1, line => by
    show pureStepsF φ (Fsac φ 0) reviewAgg n (pureAdvanceF φ (Fsac φ 0) reviewAgg line) = pureStepsW φ n (pureAdvanceW φ line)
    rw [advance_eq φ line, steps_eq n]

/-- **The improved run is the generic run with no conditioned pass.** -/
theorem run_eq : pureRunF φ (Fsac φ 0) reviewAgg = pureRunW φ := steps_eq φ _ _

theorem alongF_of_alongW (g : GPathM) (h : AlongAssignW φ a g) :
    AlongAssignF φ a (Fsac φ 0) reviewAgg g := by
  induction h with
  | seed title => exact AlongAssignF.seed title
  | up g title _ ih => exact AlongAssignF.up g title ih
  | joinL g₁ g₂ hok h₂ _ ih => exact AlongAssignF.joinL g₁ g₂ hok h₂ ih
  | joinR g₁ g₂ hok h₁ _ ih => exact AlongAssignF.joinR g₁ g₂ hok h₁ ih

theorem alongW_of_alongF (g : GPathM) (h : AlongAssignF φ a (Fsac φ 0) reviewAgg g) :
    AlongAssignW φ a g := by
  induction h with
  | seed title => exact AlongAssignW.seed title
  | up g title _ ih => exact AlongAssignW.up g title ih
  | joinL g₁ g₂ hok h₂ _ ih => exact AlongAssignW.joinL g₁ g₂ hok h₂ ih
  | joinR g₁ g₂ hok h₁ _ ih => exact AlongAssignW.joinR g₁ g₂ hok h₁ ih

-- ============================================================
-- What this module still says, now proved generically
-- ============================================================

/-- **The conservation law for the improved machine.** Along a satisfying assignment's branch, the
selection that assignment names is a sound chain of every state, and its map ids are the
assignment's own choices. -/
theorem chainSound_alongW (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignW φ a g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k := by
  obtain ⟨sel, hsel, hids⟩ := chainSound_alongF φ a (Fsac φ 0) reviewAgg hwf (prunes_Fsac φ 0)
    (keepsBranch_Fsac φ a hsat 0) g (alongF_of_alongW φ a g h)
  exact ⟨sel, hsel, fun k hk0 hk => (hids k hk0 hk).1⟩

theorem isValid_alongW (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignW φ a g) :
    isValid g = true :=
  isValid_alongF φ a (Fsac φ 0) reviewAgg hwf (prunes_Fsac φ 0) (keepsBranch_Fsac φ a hsat 0) g
    (alongF_of_alongW φ a g h)

theorem inhabited_alongW (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignW φ a g) :
    AbsSat.GraphPath.Model.Inhabited g :=
  inhabitedM_alongF φ a (Fsac φ 0) reviewAgg hwf (prunes_Fsac φ 0) (keepsBranch_Fsac φ a hsat 0) g
    (alongF_of_alongW φ a g h)

/-- **The improved driver ends holding the branch.** -/
theorem pureRunW_carries (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunW φ
      ∧ AlongAssignW φ a g ∧ g.current_step = stepCount φ := by
  obtain ⟨g, hmem, hal, hcs⟩ :=
    pureRunF_carries φ a (Fsac φ 0) reviewAgg hwf hsat (prunes_Fsac φ 0) (keepsBranch_Fsac φ a hsat 0)
  exact ⟨g, run_eq φ ▸ hmem, alongW_of_alongF φ a g hal, hcs⟩

/-- **The improved machine loses no solution.** The state parked at a satisfying assignment's final
node spans the whole map, is valid, and denotes something. -/
theorem pureRunW_full_state (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunW φ
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hmem, hcs, hv, hi⟩ :=
    pureRunF_full_state φ a (Fsac φ 0) reviewAgg hwf hsat (prunes_Fsac φ 0) (keepsBranch_Fsac φ a hsat 0)
  exact ⟨g, run_eq φ ▸ hmem, hcs, hv, hi⟩

/-- **A satisfiable formula gets a non-empty last line.** -/
theorem pureRunW_ne_nil (hwf : WF φ) (h : Satisfiable φ) : pureRunW φ ≠ [] := by
  have hne := pureRunF_ne_nil φ (Fsac φ 0) reviewAgg hwf (prunes_Fsac φ 0)
    (fun b hb => keepsBranch_Fsac φ b hb 0) h
  rw [run_eq φ] at hne
  exact hne

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ConservationImproves.chainSound_alongW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongW

/-- info: 'AbsSat.GraphPath.Model.ConservationImproves.pureRunW_full_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_full_state

/-- info: 'AbsSat.GraphPath.Model.ConservationImproves.pureRunW_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_ne_nil

end AbsSat.GraphPath.Model.ConservationImproves
