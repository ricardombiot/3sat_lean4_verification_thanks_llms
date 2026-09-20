-- lean_project/AbsSat/GraphPath/Model/PinSend.lean
import AbsSat.GraphPath.Model.PinHistory

/-!
# Pinning goes through a send

`PinAdvance` (one advance of the machine) has two parts: the sends and the union by key. This module proves
the first, with no hypothesis:

* `sup_transfer`, `sup_weak`, `sup_below_addNode` — a support relation moves along an embedding, survives
  the weak filter when its members pass it, and the part of a support below the new top node of an UP is a
  support of the state before the UP.
* **`pin_send`** — pinning `r` in the state a send produces sits inside the send of any line state that
  contains the pinned source.

So `PinAdvance` reduces to the union by key alone (`PinJoin`, `pinAdvance_of_join`).
-/

namespace AbsSat.GraphPath.Model.PinSend

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit insertPure)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_pureAdvanceW)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.BranchLines (sent)
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel Embedded sup_of_embedded mem_bounds)
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk AOk_filterAllAgg)

-- ============================================================
-- Moving a support
-- ============================================================

/-- **A support moves along an embedding.** -/
theorem sup_transfer {G B : GPathM} {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (h : Sup G S R) (e : Embedded G B) : Sup B S R := by
  have memG : ∀ p, S p → Mem G p := fun p hp => Option.isSome_iff_exists.mp (h.node p hp)
  have nodeB : ∀ p m, G.node? p = some m → ∃ n, B.node? p = some n ∧ (∀ q ∈ m.owners, Mem G q → q ∈ n.owners) ∧
      (∀ q ∈ m.parents, Mem G q → q ∈ n.parents) := e.node
  -- the node of `B` at a member is the image of `G`'s
  have img : ∀ p n, S p → B.node? p = some n → ∃ m, G.node? p = some m ∧
      (∀ q ∈ m.owners, Mem G q → q ∈ n.owners) ∧ (∀ q ∈ m.parents, Mem G q → q ∈ n.parents) := by
    intro p n hp hn
    obtain ⟨m, hm⟩ := memG p hp
    obtain ⟨n', hn', ho, hpa⟩ := nodeB p m hm
    rw [hn] at hn'; cases hn'
    exact ⟨m, hm, ho, hpa⟩
  refine ⟨fun p hp => e.gow p (h.gow p hp), fun p hp => ?_, fun p hp => ?_, h.dom, ?_, ?_, ?_, ?_, ?_,
    h.sym, ?_⟩
  · obtain ⟨m, hm⟩ := memG p hp
    obtain ⟨n, hn, _⟩ := nodeB p m hm
    rw [hn]; rfl
  · rw [← e.step]; exact h.step p hp
  · intro x v n hxv hn
    obtain ⟨m, hm, ho, _⟩ := img x n (h.dom x v hxv).1 hn
    exact ho v (h.own x v m hxv hm) (memG v (h.dom x v hxv).2)
  · intro x hx l h0 h1; exact h.cov x hx l h0 (by rw [e.step]; exact h1)
  · intro x d hx hd hpn v hxv
    obtain ⟨m, hm, _, hpa⟩ := img x d hx hd
    obtain ⟨c, hc, h1, h2, h3⟩ := h.par x m hx hm hpn v hxv
    exact ⟨c, hpa c hc (memG c (h.dom x c h1).2), h1, h2, h3⟩
  · intro x hx hs v hxv
    obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hx (by rw [e.step]; exact hs) v hxv
    obtain ⟨n, hn, _, hpa⟩ := nodeB c m hm
    exact ⟨c, n, hn, hpa x hxm (memG x hx), h1, h2, h3⟩
  · intro x v hxv l h0 h1; exact h.agg x v hxv l h0 (by rw [e.step]; exact h1)
  · intro x c d h1 h2 hs hd
    obtain ⟨m, hm, _, hpa⟩ := img x d (h.dom x c h1).1 hd
    exact hpa c (h.link x c m h1 h2 hs hm) (memG c (h.dom x c h1).2)

/-- **A support survives the weak filter when its members pass it.** The filter touches only the global
owners. -/
theorem sup_weak {B : GPathM} {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (h : Sup B S R) (ws : List (Int × List NodeId))
    (hg : ∀ p, S p → ∀ e ∈ ws, p.id.step = e.1 → p.id ∈ e.2) : Sup (filterWeakAll B ws) S R := by
  obtain ⟨hn, hs, _⟩ := filterWeakAll_frame ws B
  have hnode : ∀ x, (filterWeakAll B ws).node? x = B.node? x := by
    intro x; unfold GPathM.node?; rw [hn]
  refine ⟨fun p hp => (mem_filterWeakAll ws B p).mpr ⟨h.gow p hp, hg p hp⟩, fun p hp => ?_, fun p hp => ?_,
    h.dom, fun x v n hxv hx => h.own x v n hxv (by rw [← hnode]; exact hx), fun x hx l h0 h1 => ?_,
    fun x d hx hd => h.par x d hx (by rw [← hnode]; exact hd), fun x hx hst v hxv => ?_,
    fun x v hxv l h0 h1 => ?_, h.sym, fun x c d h1 h2 h3 hd => h.link x c d h1 h2 h3 (by rw [← hnode]; exact hd)⟩
  · rw [hnode]; exact h.node p hp
  · rw [hs]; exact h.step p hp
  · exact h.cov x hx l h0 (by rw [← hs]; exact h1)
  · obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hx (by rw [← hs]; exact hst) v hxv
    exact ⟨c, m, by rw [hnode]; exact hm, hxm, h1, h2, h3⟩
  · exact h.agg x v hxv l h0 (by rw [← hs]; exact h1)

/-- The node the UP adds sits on the new step, and its parents are the nodes one step below. -/
theorem addNode_top_parents (F : GPathM) (d : NodeId) (t : String) (hd : d.step = F.current_step)
    (hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step) (c : PathNodeId) (m : PNodeM)
    (hc : (addNode F d t).node? c = some m) (hcs : c.id.step = F.current_step) :
    ∀ x ∈ m.parents, x.id.step = F.current_step - 1 := by
  have hmem : m ∈ (addNode F d t).nodes := List.mem_of_find?_eq_some hc
  have hid := node?_id_eq _ c m hc
  have htop := RunNoBorrow.tops_addNode F d t hbelow m hmem (by rw [hid, hcs])
  have hnew := addNode_node?_new F d t hd hbelow
  rw [← hid, htop, show (⟨d, F.map_parent, none⟩ : PathNodeId) = newPid F d from rfl, hnew] at hc
  cases hc
  intro x hx
  simp only [addOwner, upNode, newParents] at hx
  split at hx
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    have := (List.mem_filter.mp hn).2
    exact eq_of_beq this
  · exact absurd hx List.not_mem_nil

/-- **Below the new top node, a support of an UP is a support of the state before it.** -/
theorem sup_below_addNode (F : GPathM) (d : NodeId) (t : String) (hd : d.step = F.current_step)
    (hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step) (hpb : Parents.PBelow F)
    {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} (h : Sup (addNode F d t) S R) :
    Sup F (fun x => S x ∧ x.id.step < F.current_step)
      (fun x v => R x v ∧ x.id.step < F.current_step ∧ v.id.step < F.current_step) := by
  have hcs : (addNode F d t).current_step = F.current_step + 1 := rfl
  have old : ∀ x n, F.node? x = some n → (addNode F d t).node? x = some (upMap F d n) :=
    fun x n hx => addNode_node?_old F d t x n hx
  have below : ∀ x m, (addNode F d t).node? x = some m → x.id.step < F.current_step →
      ∃ n, F.node? x = some n ∧ m = upMap F d n :=
    fun x m hx hs => addNode_node?_below F d t hd x m hx hs
  have notnew : ∀ v : PathNodeId, v.id.step < F.current_step → v ≠ newPid F d := by
    intro v hv he; rw [he] at hv; simp only [newPid] at hv; omega
  have ownF : ∀ x v n, F.node? x = some n → v.id.step < F.current_step → v ∈ (upMap F d n).owners →
      v ∈ n.owners := by
    intro x v n _ hv hm
    rw [upMap_owners] at hm
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h) (notnew v hv)
  have pstep : ∀ x n, F.node? x = some n → ∀ c ∈ n.parents, c.id.step + 1 = x.id.step := by
    intro x n hx c hc
    have := hpb n (List.mem_of_find?_eq_some hx) c hc
    rw [node?_id_eq F x n hx] at this; omega
  refine ⟨fun p ⟨hp, hps⟩ => ?_, fun p ⟨hp, hps⟩ => ?_, fun p ⟨hp, hps⟩ => ⟨(h.step p hp).1, hps⟩,
    fun x v ⟨hxv, hx, hv⟩ => ⟨⟨(h.dom x v hxv).1, hx⟩, ⟨(h.dom x v hxv).2, hv⟩⟩,
    fun x v n ⟨hxv, _, hv⟩ hn => ownF x v n hn hv (h.own x v _ hxv (old x n hn)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.gow p hp
    rw [addNode_gowners] at this
    rcases List.mem_append.mp this with h1 | h1
    · exact h1
    · exact absurd (List.mem_singleton.mp h1) (notnew p hps)
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    obtain ⟨n, hn, _⟩ := below p m hm hps
    rw [hn]; rfl
  · intro x ⟨hx, hxs⟩ l h0 h1
    obtain ⟨v, hxv, hvs⟩ := h.cov x hx l h0 (by rw [hcs]; omega)
    exact ⟨v, ⟨hxv, hxs, by omega⟩, hvs⟩
  · intro x dd ⟨hx, hxs⟩ hd' hpn v ⟨hxv, _, hv⟩
    obtain ⟨c, hc, h1, h2, h3⟩ := h.par x _ hx (old x dd hd') hpn v hxv
    rw [upMap_parents] at hc
    have hcs' := pstep x dd hd' c hc
    exact ⟨c, hc, ⟨h1, hxs, by omega⟩, ⟨h2, by omega, hxs⟩, ⟨h3, by omega, hv⟩⟩
  · intro x ⟨hx, hxs⟩ hst v ⟨hxv, _, hv⟩
    obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hx (by rw [hcs]; omega) v hxv
    have hcb : c.id.step < F.current_step := by
      by_cases hlt : c.id.step < F.current_step
      · exact hlt
      · exfalso
        have hcle : c.id.step < F.current_step + 1 := by
          have := (h.step c (h.dom x c h1).2).2; rw [hcs] at this; exact this
        have := addNode_top_parents F d t hd hbelow c m hm (by omega) x hxm
        omega
    obtain ⟨n, hn, rfl⟩ := below c m hm hcb
    rw [upMap_parents] at hxm
    exact ⟨c, n, hn, hxm, ⟨h1, hxs, hcb⟩, ⟨h2, hcb, hxs⟩, ⟨h3, hcb, hv⟩⟩
  · intro x v ⟨hxv, hxs, hvs⟩ l h0 h1
    obtain ⟨z, hxz, hvz, hzs⟩ := h.agg x v hxv l h0 (by rw [hcs]; omega)
    exact ⟨z, ⟨hxz, hxs, by omega⟩, ⟨hvz, hvs, by omega⟩, hzs⟩
  · intro x v ⟨hxv, hx, hv⟩; exact ⟨h.sym x v hxv, hv, hx⟩
  · intro x c dd ⟨h1, _, _⟩ ⟨h2, _, _⟩ hst hd'
    have := h.link x c _ h1 h2 hst (old x dd hd')
    rwa [upMap_parents] at this

-- ============================================================
-- Pinning goes through a send
-- ============================================================

variable (φ : Cnf)

open AbsSat.GraphPath.Model.ClauseReview (pinnedAt sent_eq)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)
open AbsSat.GraphPath.Model.BranchRun (embedded_of_pruned)
open AbsSat.GraphPath.Model.BranchLines (embedded_refl)

/-- **Pinning goes through a send.** Let `G` and `B` be states of a line with the same key, and let the
pinned, reviewed `G` sit inside `B`. Then the pinned, reviewed send of `G` to `d` sits inside the send of `B`
to `d`, which is valid. The part of the pinned send below its top is a support: it survives in `G`,
through the pin into `B`, through the weak filter and `d`'s pins, and the review. -/
theorem pin_send (hwf : WF φ) (k : Int) (key : NodeId) (G B : GPathM) (hsG : StateOkF φ k (key, G))
    (hmG : MInv φ G) (hsB : StateOkF φ k (key, B)) (hmB : MInv φ B) (r : NodeId)
    (e0 : Embedded (filterAllAgg G [r]) B) (d : NodeId) (hd : d ∈ mapSons φ key.step key.index)
    (hval : isValid (sent φ G d) = true) (hvY : isValid (filterAllAgg (sent φ G d) [r]) = true) :
    isValid (sent φ B d) = true ∧ Embedded (filterAllAgg (sent φ G d) [r]) (sent φ B d) := by
  have hdstep : d.step = k + 1 := PinHistory.dstep_of φ k (key, G) hsG d hd
  -- the sent state is `F` with `d` on top
  have hvF := ClauseReview.valid_pinned φ G d hval
  have heqG : sent φ G d = addNode (pinnedAt φ G d) d "" := by
    rw [sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hprF : Pruned G (pinnedAt φ G d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have hcsF : (pinnedAt φ G d).current_step = k + 1 := by rw [hprF.step_eq, hsG.step]
  have hRF : ReadableAgg (pinnedAt φ G d) :=
    ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmG.rctx, rfl⟩
  have rcF := RCtx_of_readableAgg _ hRF
  -- the pinned send `Y`
  have hmS := ReaderAggRun.MInv_sent φ hwf k (key, G) hsG hmG d hd hval
  have hRY : ReadableAgg (filterAllAgg (sent φ G d) [r]) := ⟨_, _, hmS.rctx, rfl⟩
  have okY : AggFixpoint.AggOk (filterAllAgg (sent φ G d) [r]) := aggOk_reviewAgg _ hvY
  have smpY := AnchoredSurvive.SMP_filterAllAgg _ hmS.smp hmS.rctx.shape.notroot [r]
  have pmsY := AggInvariants.PMS_filterAllAgg _ [r] hmS.pms
  have snY := AggInvariants.SN_filterAllAgg _ [r] hmS.sn
  have prY : Pruned (sent φ G d) (filterAllAgg (sent φ G d) [r]) := pruned_filterAllAgg _ _
  have cleanY : ∀ p, p ∈ (filterAllAgg (sent φ G d) [r]).gowners → p.id.step = r.step → p.id = r :=
    fun p hp hs => ReaderAggRun.filterAllAgg_cleans (sent φ G d) [r] r List.mem_cons_self p hp hs
  generalize hYdef : filterAllAgg (sent φ G d) [r] = Y at hRY hvY okY smpY pmsY snY prY cleanY ⊢
  have adY := AdjacentOwners.adj_of_readable _ hRY hvY pmsY snY
  have hndS : NodupIds (sent φ G d) := hmS.rctx.nodup
  have eYS0 : Embedded Y (sent φ G d) := embedded_of_pruned prY hndS (embedded_refl (sent φ G d))
  have eYS : Embedded Y (addNode (pinnedAt φ G d) d "") := by rw [← heqG]; exact eYS0
  have supS : Sup (addNode (pinnedAt φ G d) d "") (Mem Y) (Rel Y) :=
    sup_of_embedded Y (addNode (pinnedAt φ G d) d "") adY okY smpY eYS
  have supF := sup_below_addNode (pinnedAt φ G d) d "" (by rw [hdstep, hcsF]) rcF.below rcF.shape.pbelow supS
  rw [hcsF] at supF
  -- the members, the pins and the weak filter
  have gowS : ∀ p, Mem Y p → p ∈ Y.gowners := fun p hp => (sup_self _ adY okY smpY).gow p hp
  have memF : ∀ p, (Mem Y p ∧ p.id.step < k + 1) → p ∈ (pinnedAt φ G d).gowners := fun p h => supF.gow p h
  have pinsR : ∀ p, (Mem Y p ∧ p.id.step < k + 1) → p.id.step = r.step → p.id = r :=
    fun p hp hs => cleanY p (gowS p hp.1) hs
  -- into `G`, through the pin, into `B`
  have supG := sup_transfer supF (embedded_of_pruned hprF hmG.rctx.nodup (embedded_refl G))
  have supGr := (AOk_filterAllAgg G ⟨supG, hmG.smp, hmG.rctx.shape.notroot⟩ [r]
    (fun q hq p hp hs => by rw [List.mem_singleton.mp hq] at hs ⊢; exact pinsR p hp hs)).sup
  have supB := sup_transfer supGr e0
  -- through the weak filter and `d`'s pins
  have hprW : Pruned (filterWeakAll G (weakReqOfCnf φ d)) (pinnedAt φ G d) := pruned_filterAllAgg _ _
  have supBW := sup_weak supB (weakReqOfCnf φ d) (fun p hp =>
    ((mem_filterWeakAll _ G p).mp (hprW.gowners_sub p (memF p hp))).2)
  obtain ⟨hnW, _, _⟩ := filterWeakAll_frame (weakReqOfCnf φ d) B
  have smpW : Sons.SMP (filterWeakAll B (weakReqOfCnf φ d)) := by unfold Sons.SMP; rw [hnW]; exact hmB.smp
  have nrW : Parents.NotRoot (filterWeakAll B (weakReqOfCnf φ d)) := by
    unfold Parents.NotRoot; rw [hnW]; exact hmB.rctx.shape.notroot
  have supFB : Sup (pinnedAt φ B d) _ _ := (AOk_filterAllAgg _ ⟨supBW, smpW, nrW⟩ (reqOfCnf φ d)
    (fun q hq p hp hs => ReaderAggRun.filterAllAgg_cleans _ _ q hq p (memF p hp) hs)).sup
  -- the pinned send has a member below its top, so `B`'s send is valid
  have ctxY := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRY) hvY
  have hk0 : 0 ≤ k := SliceInvariant.nonneg_of_mapNodes φ k key hsG.onMap
  have hcsS : (sent φ G d).current_step = k + 2 := by
    rw [heqG]; show (pinnedAt φ G d).current_step + 1 = _; rw [hcsF]; omega
  have hcsY : Y.current_step = k + 2 := by rw [prY.step_eq, hcsS]
  have memY : ∀ q, q ∈ Y.gowners → Mem Y q := by
    intro q hq
    obtain ⟨n, hn, hnid⟩ := ctxY.gn q hq
    exact ⟨n, by rw [← hnid]; exact node?_of_mem adY.rc.nodup n hn⟩
  obtain ⟨z, hz, hzs⟩ : ∃ z, z ∈ Y.gowners ∧ z.id.step = 0 := by
    have hv' := hvY
    simp only [isValid, List.all_eq_true] at hv'
    obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp (hv' 0 (mem_intRange (Int.le_refl 0) (by rw [hcsY]; omega)))
    exact ⟨z, hz, eq_of_beq hzs⟩
  have hvFB := SupportSplit.valid_of_sup _ _ _ supFB z ⟨memY z hz, by omega⟩
  have hprFB : Pruned B (pinnedAt φ B d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have hcsFB : (pinnedAt φ B d).current_step = k + 1 := by rw [hprFB.step_eq, hsB.step]
  have heqB : sent φ B d = addNode (pinnedAt φ B d) d "" := by
    rw [sent_eq]; unfold GPathM.up; rw [hvFB]; rfl
  have hRFB : ReadableAgg (pinnedAt φ B d) :=
    ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmB.rctx, rfl⟩
  have rcFB := RCtx_of_readableAgg _ hRFB
  refine ⟨by rw [heqB]; exact ReviewJoin.isValid_addNode _ d "" hvFB (by rw [hdstep, hcsFB]), ?_⟩
  -- the embedding, node by node
  have hnew : newPid (pinnedAt φ G d) d = newPid (pinnedAt φ B d) d := by
    simp only [newPid]; rw [hprF.map_parent_eq, hprFB.map_parent_eq, hsG.par, hsB.par]
  have supYY := sup_self _ adY okY smpY
  have top : ∀ q, Mem Y q → ¬ q.id.step < k + 1 → q = newPid (pinnedAt φ G d) d := by
    intro q ⟨mq, hmq⟩ hqs
    obtain ⟨n, hn, _⟩ := eYS.node q mq hmq
    have hb := (mem_bounds _ adY ⟨mq, hmq⟩).2
    have hmem := List.mem_of_find?_eq_some hn
    have htop := RunNoBorrow.tops_addNode (pinnedAt φ G d) d "" rcF.below n hmem
      (by rw [node?_id_eq _ q n hn, hcsF]; omega)
    rw [← node?_id_eq _ q n hn, htop]; rfl
  rw [heqB]
  refine ⟨by rw [hcsY]; show _ = (pinnedAt φ B d).current_step + 1; rw [hcsFB]; omega, fun q hq => ?_,
    fun x m hm => ?_⟩
  · rw [addNode_gowners]
    by_cases hqs : q.id.step < k + 1
    · exact List.mem_append_left _ (supFB.gow q ⟨memY q hq, hqs⟩)
    · rw [top q (memY q hq) hqs, hnew]; exact List.mem_append_right _ List.mem_cons_self
  · have hxm : Mem Y x := ⟨m, hm⟩
    have hpar : ∀ q ∈ m.parents, q.id.step + 1 = x.id.step := by
      intro q hq
      have := adY.rc.shape.pbelow m (List.mem_of_find?_eq_some hm) q hq
      rw [node?_id_eq _ x m hm] at this; omega
    by_cases hxs : x.id.step < k + 1
    · obtain ⟨nF, hnF⟩ := Option.isSome_iff_exists.mp (supFB.node x ⟨hxm, hxs⟩)
      refine ⟨upMap (pinnedAt φ B d) d nF, addNode_node?_old _ d "" x nF hnF, fun q hq hqm => ?_,
        fun q hq hqm => ?_⟩
      · rw [upMap_owners]
        by_cases hqs : q.id.step < k + 1
        · exact List.mem_append_left _ (supFB.own x q nF ⟨⟨m, hm, hq, hqm⟩, hxs, hqs⟩ hnF)
        · rw [top q hqm hqs, hnew]; exact List.mem_append_right _ List.mem_cons_self
      · rw [upMap_parents]
        have hqs := hpar q hq
        have hrel : Rel Y x q := ⟨m, hm, (adY.links x m hm).1 q hq, hqm⟩
        exact supFB.link x q nF ⟨hrel, hxs, by omega⟩ ⟨supYY.sym x q hrel, by omega, hxs⟩ hqs hnF
    · have hxt := top x hxm hxs
      have hnn := addNode_node?_new (pinnedAt φ B d) d "" (by rw [hdstep, hcsFB]) rcFB.below
      refine ⟨_, by rw [hxt, hnew]; exact hnn, fun q hq hqm => ?_, fun q hq hqm => ?_⟩
      · simp only [addOwner, upNode, List.mem_append, List.mem_singleton]
        by_cases hqs : q.id.step < k + 1
        · exact Or.inl (supFB.gow q ⟨hqm, hqs⟩)
        · exact Or.inr (by rw [top q hqm hqs, hnew])
      · have hqs := hpar q hq
        have hxk : x.id.step = k + 1 := by have := (mem_bounds _ adY hxm).2; rw [hcsY] at this; omega
        obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (supFB.node q ⟨hqm, by omega⟩)
        simp only [addOwner, upNode, newParents]
        rw [if_pos (by rw [hcsFB]; omega)]
        exact mem_line_of_node? _ q nq hnq _ (by rw [hcsFB]; omega)

/-- **A valid pinned send has a valid pinned source.** The part of the pinned send below its top is a
support of the pinned source, with a member. -/
theorem pinned_source_valid (hwf : WF φ) (k : Int) (key : NodeId) (G : GPathM) (hsG : StateOkF φ k (key, G))
    (hmG : MInv φ G) (r : NodeId) (d : NodeId) (hd : d ∈ mapSons φ key.step key.index)
    (hval : isValid (sent φ G d) = true) (hvY : isValid (filterAllAgg (sent φ G d) [r]) = true) :
    isValid (filterAllAgg G [r]) = true := by
  have hdstep : d.step = k + 1 := PinHistory.dstep_of φ k (key, G) hsG d hd
  have hvF := ClauseReview.valid_pinned φ G d hval
  have heqG : sent φ G d = addNode (pinnedAt φ G d) d "" := by
    rw [sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hprF : Pruned G (pinnedAt φ G d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have hcsF : (pinnedAt φ G d).current_step = k + 1 := by rw [hprF.step_eq, hsG.step]
  have hRF : ReadableAgg (pinnedAt φ G d) :=
    ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmG.rctx, rfl⟩
  have rcF := RCtx_of_readableAgg _ hRF
  have hmS := ReaderAggRun.MInv_sent φ hwf k (key, G) hsG hmG d hd hval
  have hRY : ReadableAgg (filterAllAgg (sent φ G d) [r]) := ⟨_, _, hmS.rctx, rfl⟩
  have okY : AggFixpoint.AggOk (filterAllAgg (sent φ G d) [r]) := aggOk_reviewAgg _ hvY
  have smpY := AnchoredSurvive.SMP_filterAllAgg _ hmS.smp hmS.rctx.shape.notroot [r]
  have pmsY := AggInvariants.PMS_filterAllAgg _ [r] hmS.pms
  have snY := AggInvariants.SN_filterAllAgg _ [r] hmS.sn
  have prY : Pruned (sent φ G d) (filterAllAgg (sent φ G d) [r]) := pruned_filterAllAgg _ _
  have cleanY : ∀ p, p ∈ (filterAllAgg (sent φ G d) [r]).gowners → p.id.step = r.step → p.id = r :=
    fun p hp hs => ReaderAggRun.filterAllAgg_cleans (sent φ G d) [r] r List.mem_cons_self p hp hs
  generalize hYdef : filterAllAgg (sent φ G d) [r] = Y at hRY hvY okY smpY pmsY snY prY cleanY
  have adY := AdjacentOwners.adj_of_readable _ hRY hvY pmsY snY
  have hndS : NodupIds (sent φ G d) := hmS.rctx.nodup
  have eYS0 : Embedded Y (sent φ G d) := embedded_of_pruned prY hndS (embedded_refl (sent φ G d))
  have eYS : Embedded Y (addNode (pinnedAt φ G d) d "") := by rw [← heqG]; exact eYS0
  have supS : Sup (addNode (pinnedAt φ G d) d "") (Mem Y) (Rel Y) :=
    sup_of_embedded Y (addNode (pinnedAt φ G d) d "") adY okY smpY eYS
  have supF := sup_below_addNode (pinnedAt φ G d) d "" (by rw [hdstep, hcsF]) rcF.below rcF.shape.pbelow supS
  rw [hcsF] at supF
  have gowS : ∀ p, Mem Y p → p ∈ Y.gowners := fun p hp => (sup_self _ adY okY smpY).gow p hp
  have supG := sup_transfer supF (embedded_of_pruned hprF hmG.rctx.nodup (embedded_refl G))
  have supGr := (AOk_filterAllAgg G ⟨supG, hmG.smp, hmG.rctx.shape.notroot⟩ [r]
    (fun q hq p hp hs => by rw [List.mem_singleton.mp hq] at hs ⊢; exact cleanY p (gowS p hp.1) hs)).sup
  have ctxY := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRY) hvY
  have hk0 : 0 ≤ k := SliceInvariant.nonneg_of_mapNodes φ k key hsG.onMap
  have hcsY : Y.current_step = k + 2 := by
    rw [prY.step_eq, heqG]; show (pinnedAt φ G d).current_step + 1 = _; rw [hcsF]; omega
  have hv' := hvY
  simp only [isValid, List.all_eq_true] at hv'
  obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp (hv' 0 (mem_intRange (Int.le_refl 0) (by rw [hcsY]; omega)))
  obtain ⟨n, hn, hnid⟩ := ctxY.gn z hz
  exact SupportSplit.valid_of_sup _ _ _ supGr z
    ⟨⟨n, by rw [← hnid]; exact node?_of_mem adY.rc.nodup n hn⟩, by rw [eq_of_beq hzs]; omega⟩

-- ============================================================
-- What is left: the union by key
-- ============================================================

/-- **Pinning goes through the union by key, at line `m`.** At an entry of a branch's next line, if the
pinned, reviewed union is valid, some side's pinned send is valid, and the pinned union sits inside any
state of the next line with that key that contains every valid pinned side. -/
def PinJoinAt (m : Nat) : Prop :=
  ∀ (P : List NodeId), let L := PinHistory.branchLine φ P m
  ∀ r : NodeId, 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ p J, (p, J) ∈ pureAdvanceW φ L → isValid (filterAllAgg J [r]) = true →
      (∃ kv ∈ L, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
        isValid (filterAllAgg (sent φ kv.2 p) [r]) = true) ∧
      ∀ Z : GPathM, StateOkF φ ((m : Int) + 1) (p, Z) → MInv φ Z →
        (∀ kv ∈ L, p ∈ mapSons φ kv.1.step kv.1.index → isValid (sent φ kv.2 p) = true →
          isValid (filterAllAgg (sent φ kv.2 p) [r]) = true → Embedded (filterAllAgg (sent φ kv.2 p) [r]) Z) →
        Embedded (filterAllAgg J [r]) Z

/-- **Pinning goes through the union by key**, at every line. -/
def PinJoin : Prop := ∀ m : Nat, PinJoinAt φ m

/-- The variable stage: the union lies at or below the last literal step. -/
def PinJoinVar : Prop := ∀ m : Nat, (m : Int) + 1 < litBlock φ → PinJoinAt φ m

/-- The clause stage. -/
def PinJoinClause : Prop := ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → PinJoinAt φ m

/-- **The two stages make the whole.** -/
theorem pinJoin_of_stages (hV : PinJoinVar φ) (hC : PinJoinClause φ) : PinJoin φ := by
  intro m
  by_cases h : (m : Int) + 1 < litBlock φ
  · exact hV m h
  · exact hC m (by omega)

/-- **`PinAdvance` from the union alone.** Each valid pinned side goes through its send into the other
line (`pin_send`), and grows into the other line's entry with that key; the union follows by `PinJoin`. -/
theorem pinAdvance_of_join (hwf : WF φ) (hJ : PinJoin φ) : PinHistory.PinAdvance φ := by
  intro P m r h0 h1 hlb H kv hkv hv
  have hl := PinHistory.branchLine_inv φ hwf P m
  have hl' := PinHistory.branchLine_inv φ hwf (P ++ [r]) m
  obtain ⟨⟨kv0, hkv0, hd0, hs0, hy0⟩, hZ⟩ := hJ m P r h0 h1 hlb kv.1 kv.2 hkv hv
  generalize PinHistory.branchLine φ P m = L at hl H hkv hkv0 hZ
  generalize PinHistory.branchLine φ (P ++ [r]) m = L' at hl' H ⊢
  -- every valid pinned side reaches the other line's entry
  have side : ∀ kvi ∈ L, kv.1 ∈ mapSons φ kvi.1.step kvi.1.index → isValid (sent φ kvi.2 kv.1) = true →
      isValid (filterAllAgg (sent φ kvi.2 kv.1) [r]) = true →
      ∃ J', (kv.1, J') ∈ pureAdvanceW φ L' ∧ Embedded (filterAllAgg (sent φ kvi.2 kv.1) [r]) J' := by
    intro kvi hkvi hdi hsi hyi
    have hsok := hl.1.2 kvi hkvi
    have hvG := pinned_source_valid φ hwf m kvi.1 kvi.2 hsok (hl.2 kvi hkvi) r kv.1 hdi hsi hyi
    obtain ⟨kv', hkv', hk, e0⟩ := H kvi hkvi hvG
    have hsB : StateOkF φ m (kvi.1, kv'.2) := by rw [← hk]; exact hl'.1.2 kv' hkv'
    obtain ⟨hvB, e⟩ := pin_send φ hwf m kvi.1 kvi.2 kv'.2 hsok (hl.2 kvi hkvi) hsB (hl'.2 kv' hkv') r e0
      kv.1 hdi hsi hyi
    obtain ⟨J', hJ', hg⟩ := BranchLines.full_reach φ hwf m L' hl' kv' hkv' kv.1 (by rw [hk]; exact hdi) hvB
    exact ⟨J', hJ', BranchRun.embedded_of_grown e hg⟩
  obtain ⟨J', hJ', e0'⟩ := side kv0 hkv0 hd0 hs0 hy0
  have hl2 := LineInv_pureAdvanceW φ hwf m L' hl'
  refine ⟨(kv.1, J'), hJ', rfl, hZ J' (hl2.1.2 _ hJ') (hl2.2 _ hJ') ?_⟩
  intro kvi hkvi hdi hsi hyi
  obtain ⟨J'', hJ'', e⟩ := side kvi hkvi hdi hsi hyi
  rw [BranchLines.key_unique _ hl2.1.1 kv.1 J'' J' hJ'' hJ'] at e
  exact e

/-- **The verdict from the union by key.** -/
theorem sat_of_pinJoin (hwf : WF φ) (hJ : PinJoin φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  PinHistory.sat_of_pinAdvance φ hwf (pinAdvance_of_join φ hwf hJ) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinSend.sat_of_pinJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinJoin

end AbsSat.GraphPath.Model.PinSend
