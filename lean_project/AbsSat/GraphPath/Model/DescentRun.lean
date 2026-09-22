-- lean_project/AbsSat/GraphPath/Model/DescentRun.lean
import AbsSat.GraphPath.Model.DescentUp
import AbsSat.GraphPath.Model.DescentJoin
import AbsSat.GraphPath.Model.DescentFilter
import AbsSat.GraphPath.Model.BranchLines
import AbsSat.GraphPath.Model.NoDeadEndVerdict
import AbsSat.GraphPath.Model.PinHistory

/-!
# The descent, assembled over the run

`DescentUp`, `DescentJoin` and `DescentFilter` each do one case of the induction over how the
machine builds a state, and every one of them is proved. **Nobody composed them.** This module
does, and the result is the verdict with exactly two named hypotheses.

The composition follows the send, `upFilteringWeak g ws reqs d = up (filterAllAgg (filterWeakAll g ws) reqs) d`,
in the order the driver applies it:

* `filterWeakAll` touches **only `gowners`**, and it is absorbed: the filter case is stated for
  `filterAllAgg g reqs` for *any* `g`, so it is applied to the weakly filtered state directly.
* `filterAllAgg` — `DescentFilter.noDeadEnd_filterAllAgg_of_completion`, under `ReqCompletion`.
* `up` — `DescentUp.noDeadEnd_addNode`, with no hypothesis beyond the reader's invariants, which
  `MInv` supplies.
* `insertPure` — a send either lands on a free key, or joins what is already there, and that is
  `DescentJoin.noDeadEnd_join` under `JoinCoveredF`.

So `noDeadEnd_line` carries the descent across one advance, `noDeadEnd_run` across the whole run,
and `sat_of_descentRun` reads the verdict off it.

**What the two hypotheses are.** `ReqCompletion g reqs` — every partial chain of the filtered state
completes, inside `g`, to a full chain meeting the pins. `JoinCoveredF g₁ g₂` — a partial chain of a
join is a partial chain of one side, or extends outright. Both are measured; neither is proved.

## Two things the assembly made visible

**The descent does not propagate along the run.** `noDeadEnd_advance` never reads the previous
line: `advance_inv` starts the new line from `[]`, and each sent state gets its descent from its
**own** filter, not from the state it came from. So the induction over the run is an induction in
name only — the real content is per-send.

**And the verdict needs only the completion.** A reader's state is read after one more
`filterAllAgg`, so `DescentFilter.noDeadEnd_filterAllAgg_of_completion` applies to it directly:
`sat_of_reqCompletion` takes `ReqAll` and **not** `JoinAll`. The join and the `up` are what one
would need to *prove* the completion by induction, not to use it. That is the sharpest statement
of where the whole route now stands.
-/

namespace AbsSat.GraphPath.Model.DescentRun

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (mapSons)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit insertPure)
open AbsSat.GraphPath.Model.BranchLines (insert_src sendToW_eq advance_inv sent)
open AbsSat.GraphPath.Model.NoDeadEnd (NoDeadEnd)
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_init LineInv_steps)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)

variable (φ : Cnf)

/-- **The two obligations, named once.**

`ReqAll` is `DescentFilter.ReqCompletion` at every state the driver filters, and `JoinAll` is
`DescentJoin.JoinCoveredF` at every pair it joins. Stating them over all arguments keeps the
assembly free of bookkeeping; sharpening them to the states the run actually reaches is a
separate (and easier) exercise. -/
def ReqAll : Prop :=
  ∀ (g : GPathM) (reqs : List NodeId), DescentFilter.ReqCompletion g reqs

def JoinAll : Prop :=
  ∀ g₁ g₂ : GPathM, DescentJoin.JoinCoveredF g₁ g₂

-- ============================================================
-- One send
-- ============================================================

/-- **A send keeps the descent.** The weakly filtered state is filtered and reviewed
(`ReqCompletion`), then grown by the row (`noDeadEnd_addNode`); the reader's invariants the `up`
case asks for all come from `MInv`. -/
theorem noDeadEnd_sent (hR : ReqAll) (k : Int) (hk : 0 ≤ k) (kv : NodeId × GPathM)
    (hsok : StateOkF φ k kv) (hm : MInv φ kv.2) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hv : isValid (sent φ kv.2 d) = true) :
    NoDeadEnd (sent φ kv.2 d) := by
  -- the state under the new row, and the fact that the send makes it valid
  have hprF : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have hcsF : (ClauseReview.pinnedAt φ kv.2 d).current_step = k + 1 := by
    rw [hprF.step_eq, hsok.step]
  have hcsW : (filterWeakAll kv.2 (weakReqOfCnf φ d)).current_step = k + 1 := by
    rw [(ConservationCore.pruned_filterWeakAll kv.2 (weakReqOfCnf φ d)).step_eq, hsok.step]
  have hdstep : d.step = k + 1 := PinHistory.dstep_of φ k kv hsok d hd
  have hvF : isValid (ClauseReview.pinnedAt φ kv.2 d) = true := ClauseReview.valid_pinned φ kv.2 d hv
  have heq : sent φ kv.2 d = addNode (ClauseReview.pinnedAt φ kv.2 d) d "" := by
    rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  -- the reader's invariants the `up` case asks for, all from `MInv`
  have hrcW : Reader.RCtx (filterWeakAll kv.2 (weakReqOfCnf φ d)) :=
    RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx
  have hRF : ReadableAgg (ClauseReview.pinnedAt φ kv.2 d) := ⟨_, _, hrcW, rfl⟩
  have rcF := RCtx_of_readableAgg _ hRF
  have ctxF : Pinned.Ctx (ClauseReview.pinnedAt φ kv.2 d) :=
    Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRF) hvF
  -- the filter case, then the `up` case
  have hndF : NoDeadEnd (ClauseReview.pinnedAt φ kv.2 d) :=
    DescentFilter.noDeadEnd_filterAllAgg_of_completion _ (reqOfCnf φ d) (by rw [hcsW]; omega)
      (hR _ (reqOfCnf φ d))
  rw [heq]
  exact DescentUp.noDeadEnd_addNode _ d "" ctxF rcF.nodup (MachineOk_of_pruned hprF hm.mok)
    (by rw [hdstep, hcsF]) (by rw [hcsF]; omega) hvF rcF.below hndF

-- ============================================================
-- One advance
-- ============================================================

/-- **A send lands on a free key or joins what is there.** -/
theorem noDeadEnd_insertPure (hJ : JoinAll) (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : ∀ kv ∈ acc, NoDeadEnd kv.2) (hg : NoDeadEnd g) :
    ∀ kv ∈ insertPure acc key g, NoDeadEnd kv.2 := by
  rintro ⟨d, B⟩ hB
  rcases insert_src acc key g d B hB with ⟨_, hcase⟩ | ⟨hmem, _⟩
  · rcases hcase with rfl | ⟨e, he, rfl⟩
    · exact hg
    · show NoDeadEnd (doJoin e g)
      unfold doJoin
      split
      · next hok => exact DescentJoin.noDeadEnd_join e g hok (hacc (key, e) he) hg (hJ e g)
      · exact hacc (key, e) he
  · exact hacc (d, B) hmem

/-- **One advance keeps the descent.** -/
theorem noDeadEnd_advance (hR : ReqAll) (hJ : JoinAll) (k : Int) (hk : 0 ≤ k) (L : PureLine)
    (hLI : LineInv φ k L) :
    ∀ kv ∈ pureAdvanceW φ L, NoDeadEnd kv.2 := by
  refine advance_inv φ (fun acc => ∀ kv ∈ acc, NoDeadEnd kv.2) L ?_
    (by intro kv hkv; cases hkv)
  intro kv hkv d hd acc hacc
  rw [sendToW_eq]
  split
  · next hv =>
    exact noDeadEnd_insertPure hJ acc d _ hacc
      (noDeadEnd_sent φ hR k hk kv (hLI.1.2 kv hkv) (hLI.2 kv hkv) d hd hv)
  · exact hacc

-- ============================================================
-- The whole run
-- ============================================================

/-- The seed line: every state is an `initSeed`, and those have no dead ends outright. -/
theorem noDeadEnd_init (hJ : JoinAll) : ∀ kv ∈ pureInit φ, NoDeadEnd kv.2 := by
  suffices h : ∀ d B, (d, B) ∈ pureInit φ → NoDeadEnd B by
    rintro ⟨d, B⟩ hB; exact h d B hB
  simp only [pureInit]
  have main : ∀ (l : List NodeId) (acc : PureLine), (∀ d B, (d, B) ∈ acc → NoDeadEnd B) →
      ∀ d B, (d, B) ∈ l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc →
        NoDeadEnd B := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      refine ih _ ?_
      intro d B hB
      rcases insert_src acc x _ d B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
      · subst hdd
        rcases hB' with rfl | ⟨e, he, rfl⟩
        · exact DescentUp.noDeadEnd_initSeed d ""
        · show NoDeadEnd (doJoin e _)
          unfold doJoin
          split
          · next hok =>
            exact DescentJoin.noDeadEnd_join e _ hok (h d e he)
              (DescentUp.noDeadEnd_initSeed d "") (hJ e _)
          · exact h d e he
      · exact h d B hB'
  exact main _ [] (fun d B h => absurd h List.not_mem_nil)

/-- **The descent, across the whole run.** -/
theorem noDeadEnd_steps (hwf : WF φ) (hR : ReqAll) (hJ : JoinAll) :
    ∀ (n : Nat), ∀ kv ∈ pureStepsW φ n (pureInit φ), NoDeadEnd kv.2 := by
  intro n
  cases n with
  | zero => exact noDeadEnd_init φ hJ
  | succ n =>
    rw [RunHistory.pureStepsW_succ]
    have hLI := LineInv_steps φ hwf n 0 (pureInit φ) (LineInv_init φ hwf)
    rw [show (0 : Int) + (n : Int) = (n : Int) by omega] at hLI
    exact noDeadEnd_advance φ hR hJ (n : Int) (by omega) _ hLI

theorem noDeadEnd_run (hwf : WF φ) (hR : ReqAll) (hJ : JoinAll) :
    ∀ kv ∈ pureRunW φ, NoDeadEnd kv.2 :=
  noDeadEnd_steps φ hwf hR hJ _

/-- **The verdict, from the completion alone.** A reader's state is read after one more
`filterAllAgg`, so the filter case applies to it directly and **the join and the `up` are not
needed at all**: the descent the verdict consumes is the one the final review itself provides.
The induction over the run (`noDeadEnd_run`) is what one would need to *prove* the completion,
not to use it. -/
theorem sat_of_reqCompletion (hwf : WF φ) (hR : ReqAll)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  refine NoDeadEndVerdict.sat_of_noDeadEnd φ hwf kv hkv hv ?_
  exact DescentFilter.noDeadEnd_filterAllAgg_of_completion kv.2 [] (by
    rw [hstep]; exact ConservationCore.stepCount_pos φ) (hR kv.2 [])

/-- info: 'AbsSat.GraphPath.Model.DescentRun.noDeadEnd_sent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_sent

/-- info: 'AbsSat.GraphPath.Model.DescentRun.noDeadEnd_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_advance

/-- info: 'AbsSat.GraphPath.Model.DescentRun.noDeadEnd_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_run

/-- info: 'AbsSat.GraphPath.Model.DescentRun.sat_of_reqCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_reqCompletion

end AbsSat.GraphPath.Model.DescentRun
