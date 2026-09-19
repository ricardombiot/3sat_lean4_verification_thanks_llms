-- lean_project/AbsSat/GraphPath/Model/RunNoBorrow.lean
import AbsSat.GraphPath.Model.ConservationPrefix

/-!
# No borrowing at the machine's unions

A path of the union of two branches never mixes their tables (probe `noborrow`, v148). The reason is
the author's reading of the machine as the compressed oracle: a path of a union satisfies every
requirement, so it is a **genuine** partial solution, and every genuine partial solution ending at a
branch's top is already a path of that branch.

* **`Genuine K sel`** — `sel` spells, on steps `0 … K-1`, the branch of an assignment that satisfies the
  clauses below `K`, with the parent links the map dictates.
* **`chainSound_congr`**, **`along_parents`** — a path is fixed by its map nodes: a sound chain whose map
  nodes are an assignment's choices has that assignment's parent links, so it **is** the genuine path.
* **`line_complete`** — every state of a line contains every genuine path that ends at its key
  (`ConservationPrefix.pureStepsW_chain_below` and key uniqueness).
-/

namespace AbsSat.GraphPath.Model.RunNoBorrow

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit key_inj)
open AbsSat.GraphPath.Model.PureDriverImproves (pureStepsW pureAdvanceW sendAllW sendToW upFilteringWeak filterWeakAll)
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_steps LineInv_init)
open AbsSat.GraphPath.Model.ConservationPrefix (SatBelow satBelow_mono pureStepsW_chain_below)

variable (φ : Cnf)

-- ============================================================
-- Genuine paths
-- ============================================================

/-- **A genuine partial path**: on steps `0 … K-1`, the branch of an assignment satisfying the clauses
below `K`, with the parent links the map dictates. -/
def Genuine (K : Int) (sel : Int → PathNodeId) : Prop :=
  ∃ a, SatBelow φ a K ∧ ∀ k, 0 ≤ k → k < K →
    (sel k).id = selOfAssign φ a k ∧
      (sel k).parent_id = (if k = 0 then none else some (selOfAssign φ a (k - 1)))

theorem pid_ext {x y : PathNodeId} (h1 : x.id = y.id) (h2 : x.parent_id = y.parent_id) : x = y := by
  cases x; cases y; cases h1; cases h2; rfl

/-- A sound chain depends only on its nodes inside the steps. -/
theorem chainSound_congr (g : GPathM) (sel sel' : Int → PathNodeId) (h : ChainSound g sel')
    (hpos : 0 < g.current_step) (heq : ∀ k, 0 ≤ k → k < g.current_step → sel k = sel' k) :
    ChainSound g sel := by
  obtain ⟨⟨⟨h1, h2⟩, hpw, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨⟨fun k a b => ?_, fun k a b => ?_⟩, fun i j hi hj hi' hj' hij => ?_, fun k a b => ?_⟩,
    fun k a b => ?_, fun k a b => ?_, ?_⟩
  · rw [heq k a b]; exact h1 k a b
  · rw [heq k a (by omega), heq (k + 1) (by omega) b]; exact h2 k a b
  · rw [heq i hi hi', heq j hj hj']; exact hpw i j hi hj hi' hj' hij
  · rw [heq k a b]; exact hgow k a b
  · rw [heq k a b]; exact hself k a b
  · rw [heq k a (by omega), heq (k + 1) (by omega) b]; exact hson k a b
  · refine ⟨by rw [heq 0 (Int.le_refl _) hpos]; exact hroot.1, fun k a b => ?_⟩
    rw [heq k (by omega) b]; exact hroot.2 k a b

/-- **A sound chain whose map nodes are an assignment's choices has the map's parent links.** -/
theorem along_parents (g : GPathM) (hpmp : ParentId.PMP g) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (a : Assign) (hids : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k) :
    ∀ k, 0 ≤ k → k < g.current_step →
      (sel k).parent_id = (if k = 0 then none else some (selOfAssign φ a (k - 1))) := by
  intro k h0 h1
  by_cases hz : k = 0
  · rw [if_pos hz, hz]; exact h.root_shape.1
  · rw [if_neg hz]
    have hlink := h.chain.1.2 (k - 1) (by omega) (by omega)
    rw [show k - 1 + 1 = k by omega] at hlink
    obtain ⟨hs, _⟩ := h.chain.1.1 k h0 h1
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    rw [hm] at hlink
    have := hpmp m (List.mem_of_find?_eq_some hm) (sel (k - 1)) hlink
    rw [node?_id_eq g (sel k) m hm, hids (k - 1) (by omega) (by omega)] at this
    exact this.symm

/-- A genuine path and a chain following the same assignment coincide. -/
theorem eq_of_along (g : GPathM) (hpmp : ParentId.PMP g) (sel sel' : Int → PathNodeId)
    (h' : ChainSound g sel') (a : Assign)
    (hids' : ∀ k, 0 ≤ k → k < g.current_step → (sel' k).id = selOfAssign φ a k)
    (hsel : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k ∧
      (sel k).parent_id = (if k = 0 then none else some (selOfAssign φ a (k - 1)))) :
    ∀ k, 0 ≤ k → k < g.current_step → sel k = sel' k := by
  intro k h0 h1
  exact pid_ext ((hsel k h0 h1).1.trans (hids' k h0 h1).symm)
    ((hsel k h0 h1).2.trans (along_parents φ g hpmp sel' h' a hids' k h0 h1).symm)

-- ============================================================
-- Every state of a line holds the genuine paths ending at its key
-- ============================================================

/-- **Every state of a line contains every genuine path that ends at its key.** -/
theorem line_complete (hwf : WF φ) (m : Nat) (hm : (m : Int) + 1 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (sel : Int → PathNodeId)
    (hgen : Genuine φ ((m : Int) + 1) sel) (htop : (sel (m : Int)).id = kv.1) : ChainSound kv.2 sel := by
  obtain ⟨a, hs, hsel⟩ := hgen
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  obtain ⟨g, hmem, hcs, sel', hsc, hids⟩ :=
    pureStepsW_chain_below φ a hwf ((m : Int) + 1) (by omega) hm hs
  rw [show (((m : Int) + 1 - 1).toNat) = m by omega, show (m : Int) + 1 - 1 = m by omega] at hmem
  have hkey : selOfAssign φ a (m : Int) = kv.1 := by
    rw [← htop]; exact ((hsel m (by omega) (by omega)).1).symm
  have hsame := key_inj _ hl.1.1 (selOfAssign φ a (m : Int), g) hmem kv hkv hkey
  have hg : g = kv.2 := by rw [← hsame]
  rw [← hg]
  have hmg := hl.2 _ hmem
  have hpos : 0 < g.current_step := by rw [hcs]; omega
  refine chainSound_congr g sel sel' hsc hpos (eq_of_along φ g hmg.rctx.pmp sel sel' hsc a
    (fun k h0 h1 => (hids k h0 (by rw [← hcs]; exact h1)).1)
    (fun k h0 h1 => hsel k h0 (by rw [← hcs]; exact h1)))

/-- info: 'AbsSat.GraphPath.Model.RunNoBorrow.line_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms line_complete

-- ============================================================
-- A send holds the genuine paths through its source
-- ============================================================

open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF prunes_Fsac Fsac)
open AbsSat.GraphPath.Model.ConservationCore (chainSound_up_of_prunedR SelParent)
open AbsSat.GraphPath.Model.ConservationPrefix (keepsBranch_Fsac_below)

theorem genuine_restrict {K K' : Int} {sel : Int → PathNodeId} (h : Genuine φ K sel) (hK : K' ≤ K) :
    Genuine φ K' sel := by
  obtain ⟨a, hs, hsel⟩ := h
  exact ⟨a, satBelow_mono hs hK, fun k h0 h1 => hsel k h0 (by omega)⟩

/-- **A send holds every genuine path through its source.** The state sent from the line's state at
key `p` to `d` contains every genuine path whose last two map nodes are `p` and `d`. -/
theorem send_complete (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true)
    (sel : Int → PathNodeId) (hgen : Genuine φ ((m : Int) + 2) sel)
    (hsrc : (sel (m : Int)).id = kv.1) (htop : (sel ((m : Int) + 1)).id = d) :
    ChainSound (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") sel := by
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  have hsc := line_complete φ hwf m (by omega) kv hkv sel (genuine_restrict φ hgen (by omega)) hsrc
  obtain ⟨a, hs, hsel⟩ := hgen
  have hcs : kv.2.current_step = (m : Int) + 1 := hsok.step
  have hids : ∀ k, 0 ≤ k → k < kv.2.current_step →
      (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
    intro k h0 h1
    obtain ⟨hid, hpar⟩ := hsel k h0 (by omega)
    refine ⟨hid, ?_⟩
    by_cases hz : k = 0
    · rw [if_pos hz] at hpar; exact Or.inl hpar
    · rw [if_neg hz] at hpar; exact Or.inr ⟨k - 1, hpar⟩
  have hdsel : d = selOfAssign φ a kv.2.current_step := by
    rw [hcs, ← htop]; exact (hsel _ (by omega) (by omega)).1
  have hmp : kv.2.map_parent = none ∨ ∃ j, kv.2.map_parent = some (selOfAssign φ a j) := by
    refine Or.inr ⟨m, ?_⟩
    rw [hsok.par, ← hsrc]; exact congrArg some (hsel m (by omega) (by omega)).1
  have hkeep := keepsBranch_Fsac_below φ a ((m : Int) + 2) hs 0 d kv.2 sel hsc hids hdsel (by omega)
  obtain ⟨sel', hs', hcur, hids'⟩ := chainSound_up_of_prunedR φ a AggressiveReview.reviewAgg hwf kv.2 _
    (prunes_Fsac φ 0 d kv.2) hsok.shape hmp sel hkeep hids ""
  have hsend : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" =
      AggressiveReview.upFilteringR AggressiveReview.reviewAgg (Fsac φ 0 d kv.2)
        (reqOfCnf φ (selOfAssign φ a kv.2.current_step)) (selOfAssign φ a kv.2.current_step) "" := by
    rw [← hdsel]; rfl
  rw [hsend]
  have hmh := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv d hd hval
  rw [hsend] at hmh
  have hpos : 0 < (AggressiveReview.upFilteringR AggressiveReview.reviewAgg (Fsac φ 0 d kv.2)
      (reqOfCnf φ (selOfAssign φ a kv.2.current_step)) (selOfAssign φ a kv.2.current_step) "").current_step := by
    rw [hcur]; omega
  refine chainSound_congr _ sel sel' hs' hpos (eq_of_along φ _ hmh.rctx.pmp sel sel' hs' a
    (fun k h0 h1 => (hids' k h0 (by rw [← hcur]; exact h1)).1)
    (fun k h0 h1 => hsel k h0 (by rw [hcur, hcs] at h1; exact h1)))

/-- info: 'AbsSat.GraphPath.Model.RunNoBorrow.send_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms send_complete

-- ============================================================
-- The bookkeeping: which sources a state of the next line holds
-- ============================================================

/-- **A state of the next line knows its sources**: its top nodes are `(d, p)` for the sources `p` of
a list `S`, and it contains every genuine path through `d` whose previous map node is in `S`. -/
def SendsOk (m : Nat) (d : NodeId) (g : GPathM) : Prop :=
  ∃ S : List NodeId,
    (∀ n ∈ g.nodes, n.id.id.step = (m : Int) + 1 → ∃ p ∈ S, n.id = ⟨d, some p⟩) ∧
    ∀ sel, Genuine φ ((m : Int) + 2) sel → (sel ((m : Int) + 1)).id = d → (sel (m : Int)).id ∈ S →
      ChainSound g sel

/-- The top nodes of `addNode`: only the new node sits at the old current step. -/
theorem tops_addNode (g : GPathM) (d : NodeId) (t : String)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) :
    ∀ n ∈ (addNode g d t).nodes, n.id.id.step = g.current_step → n.id = ⟨d, g.map_parent⟩ := by
  intro n hn hs
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with h1 | h2
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp h1
    rw [upMap_id] at hs
    exact absurd hs (by have := hbelow n0 hn0; omega)
  · rw [List.mem_singleton.mp h2]; rfl

/-- **A send knows its source.** -/
theorem sendsOk_send (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    SendsOk φ m d (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  refine ⟨[kv.1], ?_, fun sel hgen htop hsrc => ?_⟩
  · -- the filtered state is valid, so `up` adds the one top node `(d, kv.1)`
    obtain ⟨F, hF⟩ : ∃ F, F = AggressiveReview.filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d))
        (reqOfCnf φ d) := ⟨_, rfl⟩
    have hup0 : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = GPathM.up F d "" := by
      rw [hF]; rfl
    have hpr : Pruned kv.2 F := by
      rw [hF]; exact Pruned.trans (ConservationCore.pruned_filterWeakAll _ _)
        (AggressiveReview.pruned_filterAllAgg _ _)
    have hvF : isValid F = true := by
      cases hc : isValid F with
      | true => rfl
      | false =>
        exfalso
        have he : GPathM.up F d "" = F := by unfold GPathM.up; rw [hc]; rfl
        rw [hup0, he, hc] at hval; cases hval
    have hup : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = addNode F d "" := by
      rw [hup0]; unfold GPathM.up; rw [hvF]; rfl
    have hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step := by
      have hR : ReaderAgg.ReadableAgg F := by
        rw [hF]
        exact ⟨_, _, ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) (hl.2 kv hkv).rctx, rfl⟩
      exact (ReaderAgg.RCtx_of_readableAgg F hR).below
    intro n hn hs
    rw [hup] at hn
    have hcsF : F.current_step = (m : Int) + 1 := hpr.step_eq.trans hsok.step
    have := tops_addNode F d "" hbelow n hn (by rw [hcsF]; exact hs)
    rw [hpr.map_parent_eq, hsok.par] at this
    exact ⟨kv.1, List.mem_singleton_self _, this⟩
  · exact send_complete φ hwf m hm kv hkv d hd hval sel hgen (List.mem_singleton.mp hsrc) htop

/-- **A union knows the sources of both sides.** -/
theorem sendsOk_join (m : Nat) (d : NodeId) (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (hnd : NodupIds (join g₁ g₂)) (h₁ : SendsOk φ m d g₁) (h₂ : SendsOk φ m d g₂) :
    SendsOk φ m d (join g₁ g₂) := by
  obtain ⟨S₁, ht₁, hc₁⟩ := h₁
  obtain ⟨S₂, ht₂, hc₂⟩ := h₂
  refine ⟨S₁ ++ S₂, fun n hn hs => ?_, fun sel hgen htop hsrc => ?_⟩
  · have hjn : (join g₁ g₂).node? n.id = some n := node?_of_mem hnd n hn
    rcases join_node?_source g₁ g₂ n.id n hjn with h1 | h2
    · obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp h1
      have hid := node?_id_eq g₁ n.id n1 hn1
      obtain ⟨p, hp, hpe⟩ := ht₁ n1 (List.mem_of_find?_eq_some hn1) (by rw [hid]; exact hs)
      exact ⟨p, List.mem_append_left _ hp, by rw [← hid]; exact hpe⟩
    · obtain ⟨n2, hn2⟩ := Option.isSome_iff_exists.mp h2
      have hid := node?_id_eq g₂ n.id n2 hn2
      obtain ⟨p, hp, hpe⟩ := ht₂ n2 (List.mem_of_find?_eq_some hn2) (by rw [hid]; exact hs)
      exact ⟨p, List.mem_append_right _ hp, by rw [← hid]; exact hpe⟩
  · rcases List.mem_append.mp hsrc with h1 | h2
    · exact ChainSound_join_left g₁ g₂ sel (hc₁ sel hgen htop h1)
    · exact ChainSound_join_right g₁ g₂ hok sel (hc₂ sel hgen htop h2)

-- ============================================================
-- No borrowing at a union
-- ============================================================

open AbsSat.GraphPath.Model.ReviewJoin (pinned)
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem)
open AbsSat.GraphPath.Model.CnfChain (decode)
open AbsSat.GraphPath.Model.MapReachable (chainOnMap_of_nodesOnMap)

/-- A path of a state of the next line that satisfies its requirements is genuine. -/
theorem genuine_of_chain (hwf : WF φ) (m : Nat) (J : GPathM) (hmJ : MInv φ J)
    (hcs : J.current_step = (m : Int) + 2) (hle : J.current_step ≤ stepCount φ)
    (sel : Int → PathNodeId) (hsc : ChainSound J sel) : Genuine φ ((m : Int) + 2) sel := by
  have hrs : MapChain.ReqSatisfying (reqOfCnf φ) J sel :=
    MapChain.reqSatisfying_of_pairwiseOwned (reqOfCnf φ) J hmJ.rf hmJ.back sel hsc.chain.1 hsc.chain.2.1
  have hcm := chainOnMap_of_nodesOnMap φ J hmJ.onMap sel hsc.chain.1
  have hids : ∀ k, 0 ≤ k → k < J.current_step → (sel k).id = selOfAssign φ (decode sel) k :=
    fun k h0 h1 => ConservationPrefix.ids_of_reqSat φ hwf J sel hsc.chain.1 hrs hcm hle k h0 h1
  refine ⟨decode sel, fun j hj hjs => ?_, fun k h0 h1 => ?_⟩
  · exact PrefixDecode.satClause_of_reqSat_prefix φ J sel hwf hsc.chain.1 hrs hcm j hj _
      (List.getElem?_eq_getElem hj) (by rw [hcs]; exact hjs)
  · rw [← hcs] at h1
    exact ⟨hids k h0 h1, along_parents φ J hmJ.rctx.pmp sel hsc (decode sel) hids k h0 h1⟩

/-- What a pinned path satisfies: its nodes passed the weak and the hard requirements. -/
theorem pinned_conds (J : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) (sel : Int → PathNodeId)
    (hsc : ChainSound (pinned J ws rq) sel) (hcs : (pinned J ws rq).current_step = J.current_step) :
    (∀ w ∈ ws, ∀ k, 0 ≤ k → k < J.current_step → k = w.1 → (sel k).id ∈ w.2) ∧
    (∀ r ∈ rq, 0 ≤ r.step → r.step < J.current_step → (sel r.step).id = r) := by
  have gw : ∀ k, 0 ≤ k → k < J.current_step →
      sel k ∈ (filterWeakAll J ws).gowners ∧ ∀ r ∈ rq, (sel k).id.step ≠ r.step ∨ (sel k).id = r := by
    intro k h0 h1
    exact LocalContradiction.mem_foldl_filterRequire rq _ _ (hsc.chain.2.2 k h0 (by rw [hcs]; exact h1))
  refine ⟨fun w hw k h0 h1 hk => ?_, fun r hr h0 h1 => ?_⟩
  · have hst := (hsc.chain.1.1 k h0 (by rw [hcs]; exact h1)).2
    exact ((PureDriverImproves.mem_filterWeakAll ws J (sel k)).mp (gw k h0 h1).1).2 w hw (by rw [hst, hk])
  · have hst := (hsc.chain.1.1 r.step h0 (by rw [hcs]; exact h1)).2
    rcases (gw r.step h0 h1).2 r hr with hne | heq
    · exact absurd hst hne
    · exact heq

/-- A path of a state that satisfies the pins is a path of the pinned state. -/
theorem pinBack (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) (sel : Int → PathNodeId)
    (hg : ChainSound g sel)
    (hw : ∀ w ∈ ws, ∀ k, 0 ≤ k → k < g.current_step → k = w.1 → (sel k).id ∈ w.2)
    (hr : ∀ r ∈ rq, 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r) :
    ChainSound (pinned g ws rq) sel := by
  have hW := ConservationCore.ChainSound_filterWeakAll ws g sel hg hw
  have hcsW : (filterWeakAll g ws).current_step = g.current_step :=
    (ConservationCore.pruned_filterWeakAll g ws).step_eq
  exact ChainSound_foldl_filterRequire rq _ sel hW (fun r h0 h1 h2 => hr r h0 h1 (by rw [← hcsW]; exact h2))

/-- **No borrowing at a union of the machine**: two states of the next line that know their sources
(`SendsOk`) have no mixed path in their pinned union, whatever the pins. -/
theorem noBorrow_union (hwf : WF φ) (m : Nat) (d : NodeId) (e h : GPathM)
    (hse : StateOkF φ ((m : Int) + 1) (d, e)) (hsh : StateOkF φ ((m : Int) + 1) (d, h))
    (hme : MInv φ e) (hmh : MInv φ h) (hle : (m : Int) + 2 ≤ stepCount φ)
    (hoe : SendsOk φ m d e) (hoh : SendsOk φ m d h)
    (ws : List (Int × List NodeId)) (rq : List NodeId) (sel : Int → PathNodeId)
    (hsc : ChainSound (join (pinned e ws rq) (pinned h ws rq)) sel) :
    ChainSound (pinned e ws rq) sel ∨ ChainSound (pinned h ws rq) sel := by
  have hok := ConservationFilter.okJoin_of_stateOkF φ _ d e h hse hsh
  have hmJ := ReaderAggRun.MInv_join φ e h hok hme hmh
  have hcsJ : (join e h).current_step = (m : Int) + 2 := by
    rw [(grown_join_left e h).step_eq, hse.step]; omega
  have hpJ : pinned (join e h) ws rq = join (pinned e ws rq) (pinned h ws rq) := by
    show rq.foldl filterRequire (filterWeakAll (join e h) ws) = _
    rw [ReviewJoin.filterWeakAll_join, ReviewJoin.foldl_filterRequire_join]
  have hprJ : Pruned (join e h) (pinned (join e h) ws rq) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_foldl filterRequire pruned_filterRequire rq _)
  rw [← hpJ] at hsc
  have hscJ := SubsetSemantics.ChainSound_of_pruned hprJ hmJ.rctx.nodup hmJ.smp sel hsc
  have hgen := genuine_of_chain φ hwf m (join e h) hmJ hcsJ (by rw [hcsJ]; exact hle) sel hscJ
  obtain ⟨hwk, hrq⟩ := pinned_conds (join e h) ws rq sel hsc hprJ.step_eq
  -- the source of the path's top
  have hsrc : (sel ((m : Int) + 1)).parent_id = some (sel (m : Int)).id := by
    obtain ⟨a, _, hsel⟩ := hgen
    rw [(hsel _ (by omega) (by omega)).2, if_neg (by omega), (hsel m (by omega) (by omega)).1,
      show (m : Int) + 1 - 1 = m by omega]
  have htopR : Mem (join e h) (sel ((m : Int) + 1)) :=
    PartSplitReal.mem_of_chain _ sel hscJ ((m : Int) + 1) (by omega) (by rw [hcsJ]; omega)
  have hst : (sel ((m : Int) + 1)).id.step = (m : Int) + 1 := (hscJ.chain.1.1 _ (by omega) (by rw [hcsJ]; omega)).2
  -- a genuine path whose top is on a side is a path of that side, then of the pinned side
  have side : ∀ g, StateOkF φ ((m : Int) + 1) (d, g) → SendsOk φ m d g →
      Mem g (sel ((m : Int) + 1)) → ChainSound (pinned g ws rq) sel := by
    intro g hsg ⟨S, htops, hcomp⟩ ⟨ng, hng⟩
    have hngid := node?_id_eq g _ ng hng
    obtain ⟨p, hp, hpe⟩ := htops ng (List.mem_of_find?_eq_some hng) (by rw [hngid]; exact hst)
    rw [hngid] at hpe
    have hpd : (sel ((m : Int) + 1)).id = d := by rw [hpe]
    have hpp : (sel (m : Int)).id = p := by
      have := hsrc; rw [hpe] at this; exact (Option.some.inj this).symm
    have hg := hcomp sel hgen hpd (by rw [hpp]; exact hp)
    have hcsg : g.current_step = (join e h).current_step := by rw [hsg.step, hcsJ]; omega
    exact pinBack g ws rq sel hg (fun w hw' k h0 h1 hk => hwk w hw' k h0 (by rw [← hcsg]; exact h1) hk)
      (fun r hr' h0 h1 => hrq r hr' h0 (by rw [← hcsg]; exact h1))
  rcases JoinSide.mem_side e h (join e h) (Pruned.refl _) hmJ.rctx.nodup htopR with he' | hh'
  · exact Or.inl (side e hse hoe he')
  · exact Or.inr (side h hsh hoh hh')

/-- info: 'AbsSat.GraphPath.Model.RunNoBorrow.noBorrow_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noBorrow_union

-- ============================================================
-- The bookkeeping along the fold that builds a line
-- ============================================================

/-- **The accumulator of the next line**: the line invariant, and every state knows its sources. -/
def Acc (m : Nat) (next : PureLine) : Prop :=
  LineInv φ ((m : Int) + 1) next ∧ ∀ x ∈ next, SendsOk φ m x.1 x.2

theorem acc_nil (m : Nat) : Acc φ m [] :=
  ⟨⟨⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩, fun _ h => absurd h List.not_mem_nil⟩,
    fun _ h => absurd h List.not_mem_nil⟩

/-- **One send keeps the bookkeeping**: inserting a send either adds a new key (the send knows its
source) or joins it into the state of its key (the union knows both lists of sources). -/
theorem acc_sendToW (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index) (next : PureLine) (hacc : Acc φ m next) :
    Acc φ m (sendToW φ kv.2 next d) := by
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  refine ⟨ReaderAggRun.LineInv_sendToW φ hwf m kv hsok hmkv d hd next hacc.1, ?_⟩
  unfold sendToW
  split
  · next hval =>
    have hsend := sendsOk_send φ hwf m hm kv hkv d hd hval
    have hmh := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv d hd hval
    have hsh := ConservationFilter.StateOkF_sent φ (Fsac φ 0) AggressiveReview.reviewAgg (prunes_Fsac φ 0)
      m kv hsok d hd hval
    unfold insertPure
    split
    · next k' e0 hf =>
      have hmem : (k', e0) ∈ next := List.mem_of_find?_eq_some hf
      have hk' : k' = d := eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == d) hf)
      intro x hx
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
      cases hb : y.1 == d with
      | true =>
        rw [hb] at hxy
        simp only [if_true] at hxy
        rw [← hxy]
        have he0 : SendsOk φ m d e0 := by have := hacc.2 _ hmem; rw [hk'] at this; exact this
        show SendsOk φ m d (doJoin e0 _)
        unfold doJoin
        split
        · next hok =>
          have hse0 : StateOkF φ ((m : Int) + 1) (d, e0) := by
            have := hacc.1.1.2 _ hmem; rw [hk'] at this; exact this
          have hme0 : MInv φ e0 := hacc.1.2 _ hmem
          exact sendsOk_join φ m d e0 _ hok (ReaderAggRun.MInv_join φ e0 _ hok hme0 hmh).rctx.nodup he0 hsend
        · exact he0
      | false =>
        rw [hb] at hxy
        simp only [Bool.false_eq_true, if_false] at hxy
        rw [← hxy]; exact hacc.2 y hy
    · intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact hacc.2 x h1
      · rw [List.mem_singleton.mp h2]; exact hsend
  · exact hacc.2

/-- **No borrowing at the unions the driver performs.** When a send is inserted at a key that already
holds a state, the two know their sources, so their pinned union has no mixed path — for any pins, in
particular those of the next destination, where the machine reviews the union. -/
theorem noBorrow_at_insert (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true)
    (next : PureLine) (hacc : Acc φ m next) (e : GPathM) (he : (d, e) ∈ next)
    (ws : List (Int × List NodeId)) (rq : List NodeId) (sel : Int → PathNodeId)
    (hsc : ChainSound (join (pinned e ws rq)
      (pinned (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") ws rq)) sel) :
    ChainSound (pinned e ws rq) sel ∨
      ChainSound (pinned (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") ws rq) sel := by
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  exact noBorrow_union φ hwf m d e _ (hacc.1.1.2 _ he)
    (ConservationFilter.StateOkF_sent φ (Fsac φ 0) AggressiveReview.reviewAgg (prunes_Fsac φ 0) m kv hsok d hd hval)
    (hacc.1.2 _ he) (ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv d hd hval) hm (hacc.2 _ he)
    (sendsOk_send φ hwf m hm kv hkv d hd hval) ws rq sel hsc

/-- info: 'AbsSat.GraphPath.Model.RunNoBorrow.acc_sendToW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms acc_sendToW

/-- info: 'AbsSat.GraphPath.Model.RunNoBorrow.noBorrow_at_insert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noBorrow_at_insert

end AbsSat.GraphPath.Model.RunNoBorrow
