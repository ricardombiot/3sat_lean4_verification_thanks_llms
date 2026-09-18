-- lean_project/AbsSat/GraphPath/Model/RoundInvariant.lean
import AbsSat.GraphPath.Model.SliceInvariant

/-!
# The round invariant: after the base review, every ghost is detectable as a pair

The author's review (v140): pins break partial paths; the base review (clean against the global owners,
coherence with parents, coherence with sons) removes the nodes left without a path; the aggressive
filter has two legs — **symmetry** and **path membership** (two owners share an owner at every step) —
and everything repeats until it converges.

Measured (probe `helly ghosts`, every map pin on every exact state of K4 and parity, 3,02 M ghost
entries — entries no surviving path holds): **every ghost dies in the first pass of the base review or
in the first aggressive sweep**, and **every ghost that reaches the sweep is directly detectable**:
asymmetric, or with a step where the two tables share nothing. No second round is ever needed.

This module turns that into the open statement, and proves that it is enough:

* **`GhostsDetectable B R`** — after the base review `B` of the pinned state, every entry is asymmetric,
  or fails path membership, or lies on a path of the final state `R`.
* **`tablesSound_of_ghosts`** — then every table of `R` is a slice. No reasoning about the order of the
  sweep is needed: the final state is symmetric and shares every step (`aggOk_reviewAgg`), and its
  tables sit inside `B`'s, so a detectable entry of `B` cannot survive into `R`.
* **`filterSlices_of_ghosts`** and **`sat_of_ghosts`** — the slice invariant of the whole run, and the
  verdict, from the round invariant.
-/

namespace AbsSat.GraphPath.Model.RoundInvariant

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk aggOk_reviewAgg)
open AbsSat.GraphPath.Model.SliceInvariant (FilterSlices sat_of_slices)

variable (φ : Cnf)

/-- **The round invariant.** After the base review `B`, every entry between two nodes is asymmetric,
or its two tables share nothing at some step, or it lies on a path of the final state `R`. -/
def GhostsDetectable (B R : GPathM) : Prop :=
  ∀ x v nx nv, B.node? x = some nx → B.node? v = some nv →
    0 ≤ x.id.step → x.id.step < B.current_step → 0 ≤ v.id.step → v.id.step < B.current_step →
    v ∈ nx.owners →
      x ∉ nv.owners ∨ sharesEveryStep B.current_step nx.owners nv.owners = false ∨ Realizes R x v

-- ============================================================
-- Detectable entries do not survive
-- ============================================================

/-- Path membership fails for smaller tables too, as long as the smaller second table still has an
entry at every step. -/
theorem shares_false_of_sub (cs : Int) (xo wo xo' wo' : List PathNodeId)
    (hx : ∀ r ∈ xo', r ∈ xo) (hw : ∀ r ∈ wo', r ∈ wo)
    (hent : ∀ k, 0 ≤ k → k < cs → hasStepEntry wo' k = true)
    (h : sharesEveryStep cs xo wo = false) : sharesEveryStep cs xo' wo' = false := by
  cases hb : sharesEveryStep cs xo' wo' with
  | false => rfl
  | true =>
    -- if the smaller tables shared every step, so would the larger ones
    have hbig : sharesEveryStep cs xo wo = true := by
      unfold sharesEveryStep at hb ⊢
      apply List.all_eq_true.mpr
      intro k hk
      have hk' := List.all_eq_true.mp hb k hk
      have h0 := mem_intRange_lower hk
      have h1 := mem_intRange_upper hk
      rw [hent k h0 (by omega), Bool.not_true, Bool.false_or] at hk'
      obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp hk'
      have hr' : r ∈ ownersAt xo k := by
        simp only [ownersAt, List.mem_filter] at hr ⊢
        exact ⟨hx r hr.1, hr.2⟩
      have hin : r ∈ wo := hw r (List.mem_of_elem_eq_true hc)
      have hany : (ownersAt xo k).any (fun r => wo.contains r) = true :=
        List.any_eq_true.mpr ⟨r, hr', List.elem_eq_true_of_mem hin⟩
      rw [hany, Bool.or_true]
    rw [hbig] at h
    exact absurd h (by decide)

/-- **The round invariant is enough**: if every entry of the base review is detectable or on a path
of the final state, every table of the final state is a slice. -/
theorem tablesSound_of_ghosts (B R : GPathM) (hpr : Pruned B R) (hndB : NodupIds B)
    (hR : ReadableAgg R) (hv : isValid R = true) (hok : AggOk R) (hG : GhostsDetectable B R) :
    TablesSound R := by
  have rc := RCtx_of_readableAgg R hR
  have ctx := Reader.Ctx_of_readable R (readable_of_readableAgg R hR) hv
  have hcs : R.current_step = B.current_step := hpr.step_eq
  -- a node of `R` is a node of `B` with a larger table
  have up : ∀ y m, R.node? y = some m → ∃ n, B.node? y = some n ∧ ∀ q ∈ m.owners, q ∈ n.owners := by
    intro y m hy
    have hmem := List.mem_of_find?_eq_some hy
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m hmem
    have hyid := node?_id_eq R y m hy
    refine ⟨n, ?_, hown⟩
    rw [← hyid, hid]; exact node?_of_mem hndB n hn
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  -- `q` is a node of `R`: an owner in range is a global owner, and global owners are nodes
  obtain ⟨mq, hmq, hmqid⟩ := rc.gn q (ctx.ownGow x n hx q hqn hq0 hq1)
  have hq : R.node? q = some mq := by rw [← hmqid]; exact node?_of_mem rc.nodup mq hmq
  obtain ⟨nx, hnx, hsubx⟩ := up x n hx
  obtain ⟨nq, hnq, hsubq⟩ := up q mq hq
  have hvx := ctx.nodeval x n hx
  have hvq := ctx.nodeval q mq hq
  obtain ⟨hsym, hshare⟩ := hok x n q mq hx hq hx0 hx1 hq0 hq1 hqn hvx hvq
  rcases hG x q nx nq hnx hnq hx0 (by rw [← hcs]; exact hx1) hq0 (by rw [← hcs]; exact hq1)
    (hsubx q hqn) with hasym | hsh | hreal
  · exact absurd (hsubq x hsym) hasym
  · -- path membership fails in `B`, so it fails in `R`
    have hent : ∀ k, 0 ≤ k → k < B.current_step → hasStepEntry mq.owners k = true := by
      intro k h0 h1
      have := owners_ok_of_isValidNode R mq hvq
      simp only [List.all_eq_true] at this
      exact this k (mem_intRange h0 (by rw [hcs]; omega))
    have := shares_false_of_sub B.current_step nx.owners nq.owners n.owners mq.owners hsubx hsubq hent hsh
    rw [← hcs] at this
    rw [hshare] at this
    exact absurd this (by decide)
  · exact hreal

-- ============================================================
-- The base review comes first
-- ============================================================

/-- The final state of the aggressive review is a narrowing of its first base review. -/
theorem pruned_review_reviewAgg (g : GPathM) : Pruned (review g) (reviewAgg g) := by
  unfold reviewAgg
  generalize measure g + 1 = fuel
  cases fuel with
  | zero => exact Pruned.refl _
  | succ n =>
    simp only [reviewAggFuel]
    split
    · split
      · exact Pruned.trans (pruned_aggSweep _) (pruned_reviewAggFuel n _)
      · exact Pruned.refl _
    · exact Pruned.refl _

/-- The pinned state a send reviews. -/
abbrev pinnedW (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) : GPathM :=
  rq.foldl filterRequire (filterWeakAll g ws)

/-- **The round invariant along the run**: after the base review of every pinned line state, every
ghost is detectable. -/
def GhostsLine : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → TablesSound kv.2 →
    ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
      isValid (filterAllAgg (filterWeakAll kv.2 ws) rq) = true →
      GhostsDetectable (review (pinnedW kv.2 ws rq)) (filterAllAgg (filterWeakAll kv.2 ws) rq)

/-- **The slice invariant from the round invariant.** -/
theorem filterSlices_of_ghosts (hG : GhostsLine φ) : FilterSlices φ := by
  intro k kv hkv hm ht ws rq hv
  have hR : ReadableAgg (filterAllAgg (filterWeakAll kv.2 ws) rq) :=
    ⟨filterWeakAll kv.2 ws, rq, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rcP : Reader.RCtx (pinnedW kv.2 ws rq) :=
    RCtx_of_keeps (keeps_foldl _ keeps_filterRequire rq _)
      (RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx)
  have hndB : NodupIds (review (pinnedW kv.2 ws rq)) := (RCtx_review _ rcP).nodup
  exact tablesSound_of_ghosts _ _ (pruned_review_reviewAgg (pinnedW kv.2 ws rq)) hndB hR hv
    (aggOk_reviewAgg _ hv) (hG k kv hkv hm ht ws rq hv)

/-- **The Improves verdict from the round invariant.** -/
theorem sat_of_ghosts (hwf : WF φ) (hG : GhostsLine φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_slices φ hwf (filterSlices_of_ghosts φ hG) kv hkv hv


/-- info: 'AbsSat.GraphPath.Model.RoundInvariant.sat_of_ghosts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_ghosts

end AbsSat.GraphPath.Model.RoundInvariant
