-- lean_project/AbsSat/GraphPath/Model/ReaderAggRun.lean
import AbsSat.GraphPath.Model.ReaderAgg
import AbsSat.GraphPath.Model.ConservationImproves
import AbsSat.GraphPath.Model.PrefixDecode
import AbsSat.GraphPath.Model.ParentOwners
import AbsSat.GraphPath.Model.AnchoredSurvive
import AbsSat.GraphPath.Model.AggInvariants

/-!
# The reader on the Improves machine: validity of the verdict reduced to one pin

`ReaderAgg` closes the reading loop over the aggressive review for any state carrying the reader's
invariants (`RCtx`). This module supplies those invariants for **every state the Improves machine
builds** (`pureRunW`), and turns the path the reader finds into a model of `φ`.

* `MInv φ g` — the reader's invariants (`RCtx`), `MachineOk`, the top-line parent id (`TL`), and the
  three facts the decoding reads: owner tables agree with requirements (`ReqFiltered`), requirements
  point backwards, and nodes are map nodes.
* `MInv_sent`, `MInv_join`, `MInv_initSeed` — each driver operation keeps it. The weak filter and the
  aggressive review only narrow (`Keeps`); `addNode` and `join` go through the existing lemmas.
* `pureRunW_state` — every state of the final line carries it.
* `sat_of_denot_final` — a path through a final state spells a model (the base machine's decoding,
  `PrefixDecode.satUpTo_of_chain`, restated over `MInv` instead of `MapReachable`).
* **`sat_of_pickSomeAgg`** — for a state of the final line: if the reader, starting after one
  aggressive review, finds at every state it visits some valid pin, then **φ is satisfiable**.

So the soundness of the Improves verdict is reduced to `PickSomeAgg` along the reader's own states.
-/

namespace AbsSat.GraphPath.Model.ReaderAggRun

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.Reader (RCtx)
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.MapReachable (NodesOnMap NodesOnMap_of_pruned NodesOnMap_up
  NodesOnMap_join NodesOnMap_initSeed ChainOnMap chainOnMap_of_nodesOnMap)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF LineOkF upFilteringF sendToF sendAllF
  pureAdvanceF pureStepsF pureRunF Fsac prunes_Fsac LineOkF_insertPure StateOkF_sent
  stateOkF_initSeed okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.ConservationImproves (run_eq)

variable (φ : Cnf)

-- ============================================================
-- The invariant
-- ============================================================

/-- Requirements point strictly backwards. -/
def ReqBack (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ req ∈ reqOfCnf φ n.id.id, req.step < n.id.id.step

structure MInv (g : GPathM) : Prop where
  rctx : RCtx g
  mok : MachineOk g
  tl : ParentId.TL g
  rf : ReqFiltered (reqOfCnf φ) g
  back : ReqBack φ g
  onMap : NodesOnMap φ g
  smp : Sons.SMP g
  pms : Sons.PMS g
  sn : Sons.SN g
  /-- The owners of a node are nodes. -/
  own : ∀ n ∈ g.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode g q

-- ============================================================
-- Narrowings
-- ============================================================

theorem keeps_review (g : GPathM) : Keeps g (review g) :=
  ⟨pruned_review g, GownersNodes.GN_review g, Parents.PN_review g, NodeIds.ids_review g⟩

theorem keeps_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM), Keeps g (reviewAggFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact keeps_review g
  | succ n ih =>
    intro g
    simp only [reviewAggFuel]
    split
    · split
      · exact Keeps.trans (keeps_review g) (Keeps.trans (keeps_aggSweep _) (ih _))
      · exact keeps_review g
    · exact keeps_review g

theorem keeps_filterAllAgg (g : GPathM) (reqs : List NodeId) : Keeps g (filterAllAgg g reqs) :=
  Keeps.trans (keeps_foldl _ keeps_filterRequire reqs g) (keeps_reviewAggFuel _ _)

theorem keeps_filterWeak (g : GPathM) (e : Int × List NodeId) : Keeps g (filterWeak g e) :=
  ⟨ConservationCore.pruned_filterWeak g e,
    fun h q hq => h q (List.mem_filter.mp hq).1, fun h => h, List.Sublist.refl _⟩

theorem keeps_filterWeakAll (g : GPathM) (ws : List (Int × List NodeId)) :
    Keeps g (filterWeakAll g ws) :=
  keeps_foldl _ keeps_filterWeak ws g

theorem MInv_of_keeps {g g' : GPathM} (hk : Keeps g g') (h : MInv φ g) (hsmp : Sons.SMP g')
    (hpms : Sons.PMS g') (hsn : Sons.SN g')
    (hown : ∀ n ∈ g'.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode g' q) :
    MInv φ g' where
  rctx := RCtx_of_keeps hk h.rctx
  mok := MachineOk_of_pruned hk.1 h.mok
  tl := ParentId.TL_of_pruned hk.1 h.tl
  rf := by
    intro n' hn' req hreq q hq hstep
    obtain ⟨n, hn, hid, hown, _⟩ := hk.1.nodes_derived n' hn'
    rw [hid] at hreq
    exact h.rf n hn req hreq q (hown q hq) hstep
  back := by
    intro n' hn' req hreq
    obtain ⟨n, hn, hid, _, _⟩ := hk.1.nodes_derived n' hn'
    rw [hid] at hreq ⊢
    exact h.back n hn req hreq
  onMap := NodesOnMap_of_pruned φ hk.1 h.onMap
  smp := hsmp
  pms := hpms
  sn := hsn
  own := hown

/-- The pins leave, at each pinned step, only the pinned map node among the global owners. -/
theorem foldl_filterRequire_cleans (g : GPathM) (reqs : List NodeId) :
    ∀ req ∈ reqs, ∀ q ∈ (reqs.foldl filterRequire g).gowners,
      q.id.step = req.step → q.id = req := by
  induction reqs generalizing g with
  | nil => intro req h; cases h
  | cons r rs ih =>
    intro req hreq q hq heq
    simp only [List.foldl_cons] at hq
    rcases List.mem_cons.mp hreq with rfl | hmem
    · have hpr : Pruned (filterRequire g req) (rs.foldl filterRequire (filterRequire g req)) :=
        pruned_foldl _ pruned_filterRequire rs _
      exact filterRequire_cleans_gowner g req q (hpr.gowners_sub q hq) heq
    · exact ih (filterRequire g r) req hmem q hq heq

theorem filterAllAgg_cleans (g : GPathM) (reqs : List NodeId) (req : NodeId) (hreq : req ∈ reqs)
    (q : PathNodeId) (hq : q ∈ (filterAllAgg g reqs).gowners) (heq : q.id.step = req.step) :
    q.id = req :=
  foldl_filterRequire_cleans g reqs req hreq q ((pruned_reviewAgg _).gowners_sub q hq) heq

-- ============================================================
-- Growth
-- ============================================================

theorem MInv_addNode (hwf : WF φ) (F : GPathM) (d : NodeId) (title : String)
    (hd : d.step = F.current_step) (hdm : d ∈ mapNodes φ d.step) (hv : isValid F = true)
    (hcl : ∀ req ∈ reqOfCnf φ d, ∀ q ∈ F.gowners, q.id.step = req.step → q.id = req)
    (h : MInv φ F) : MInv φ (addNode F d title) := by
  have hc := h.rctx
  have hBelow : SelfOwn.Below F := fun n hn => ⟨hc.snn n hn, hc.below n hn⟩
  have hup : up F d title = addNode F d title := by simp only [GPathM.up, hv, if_pos]
  refine ⟨⟨SelfOwn.OOS_addNode F d title hd hc.below hc.gn hc.oos,
      SelfOwn.SNN_addNode F d title hd h.mok hc.snn, GownersNodes.GN_addNode F d title hc.gn,
      ⟨Parents.PN_addNode F d title hc.shape.pn, Parents.PBelow_addNode F d title hd hc.shape.pbelow,
        Parents.NotRoot_addNode F d title hd h.mok hc.shape.notroot⟩,
      Sons.RootAtZero_addNode F d title hd h.mok hc.rootz, ParentId.PMP_addNode F d title h.tl hc.pmp,
      ParentId.GPMP_addNode F d title hc.gpmp,
      SelfOwn.OwnBelow_addNode F d title hd hc.ownb,
      fun n hn => (SelfOwn.Below_addNode F d title hd h.mok hBelow n hn).2,
      Reader.nodup_addNode F d title hc.nodup hc.below hd⟩,
    MachineOk_addNode F d title h.mok, ParentId.TL_addNode F d title hd hc.below, ?_, ?_,
    by rw [← hup]; exact NodesOnMap_up φ F d title hdm h.onMap,
    Sons.SMP_addNode F d title hd hc.below hc.shape.pbelow h.smp,
    Sons.PMS_addNode F d title hd hc.below h.sn h.pms, Sons.SN_addNode F d title h.sn, ?_⟩
  · intro n' hn' req hreq q hq hstepq
    rcases ParentOwners.mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | ⟨pid, hpid, rfl⟩
    · rw [upMap_id] at hreq
      rw [upMap_owners] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact h.rf m hm req hreq q hq hstepq
      · exfalso
        have h1 := h.back m hm req hreq
        have h2 := hc.below m hm
        have h3 : q.id.step = d.step := by
          rw [mapId_of_mem_newRowIds F d q (gainedOwners_subset F d m q hq)]
        omega
    · rw [rowNode_id, mapId_of_mem_newRowIds F d pid hpid] at hreq
      rw [rowNode_owners] at hq
      have hreq' : req ∈ reqOfCnf φ d := hreq
      rcases rowOwners_mem_gowners_or_self F d pid q hq with hq | rfl
      · exact hcl req hreq' q hq hstepq
      · exfalso
        have h1 := reqOfCnf_backward φ hwf d req hreq'
        have h3 : q.id.step = d.step := by rw [mapId_of_mem_newRowIds F d q hpid]
        omega
  · intro n' hn' req hreq
    rcases ParentOwners.mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | ⟨pid, hpid, rfl⟩
    · rw [upMap_id] at hreq ⊢
      exact h.back m hm req hreq
    · rw [rowNode_id, mapId_of_mem_newRowIds F d pid hpid] at hreq ⊢
      exact reqOfCnf_backward φ hwf d req hreq
  · -- owners are nodes
    have hup_old : ∀ q, GownersNodes.HasNode F q → GownersNodes.HasNode (addNode F d title) q := by
      rintro q ⟨m, hmm, hmid⟩
      refine ⟨upMap F d m, ?_, by rw [upMap_id]; exact hmid⟩
      rw [addNode_nodes]; exact List.mem_append_left _ (List.mem_map.mpr ⟨m, hmm, rfl⟩)
    have hup_new : ∀ z ∈ newRowIds F d, GownersNodes.HasNode (addNode F d title) z := by
      intro z hz
      refine ⟨rowNode F d title z, ?_, rfl⟩
      rw [addNode_nodes]; exact List.mem_append_right _ (List.mem_map_of_mem hz)
    intro n' hn' q hq
    rcases ParentOwners.mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | ⟨pid, hpid, rfl⟩
    · rw [upMap_owners] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hup_old q (h.own m hm q hq)
      · exact hup_new q (gainedOwners_subset F d m q hq)
    · rw [rowNode_owners] at hq
      rcases rowOwners_mem_gowners_or_self F d pid q hq with hq | rfl
      · exact hup_old q (hc.gn q hq)
      · exact hup_new q hpid

theorem MInv_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (h₁ : MInv φ g₁) (h₂ : MInv φ g₂) :
    MInv φ (join g₁ g₂) := by
  have c₁ := h₁.rctx
  have c₂ := h₂.rctx
  have hB₁ : SelfOwn.Below g₁ := fun n hn => ⟨c₁.snn n hn, c₁.below n hn⟩
  have hB₂ : SelfOwn.Below g₂ := fun n hn => ⟨c₂.snn n hn, c₂.below n hn⟩
  refine ⟨⟨SelfOwn.OOS_join g₁ g₂ c₁.oos c₂.oos, SelfOwn.SNN_join g₁ g₂ c₁.snn c₂.snn,
      GownersNodes.GN_join g₁ g₂ c₁.gn c₂.gn,
      ⟨Parents.PN_join g₁ g₂ c₁.shape.pn c₂.shape.pn,
        Parents.PBelow_join g₁ g₂ c₁.shape.pbelow c₂.shape.pbelow,
        Parents.NotRoot_join g₁ g₂ c₁.shape.notroot c₂.shape.notroot⟩,
      Sons.RootAtZero_join g₁ g₂ c₁.rootz c₂.rootz, ParentId.PMP_join g₁ g₂ c₁.pmp c₂.pmp,
      ParentId.GPMP_join g₁ g₂ c₁.gpmp c₂.gpmp,
      SelfOwn.OwnBelow_join g₁ g₂ hok c₁.ownb c₂.ownb,
      fun n hn => (SelfOwn.Below_join g₁ g₂ hok hB₁ hB₂ n hn).2,
      Reader.nodup_join g₁ g₂ c₁.nodup c₂.nodup⟩,
    Certifies.MachineOk_join g₁ g₂ h₁.mok, ParentId.TL_join g₁ g₂ hok h₁.tl h₂.tl,
    join_preserves_ReqFiltered (reqOfCnf φ) h₁.rf h₂.rf hok, ?_,
    NodesOnMap_join φ g₁ g₂ h₁.onMap h₂.onMap,
    Sons.SMP_join g₁ g₂ c₁.shape.pn c₂.shape.pn h₁.smp h₂.smp,
    Sons.PMS_join g₁ g₂ h₁.sn h₂.sn h₁.pms h₂.pms, Sons.SN_join g₁ g₂ h₁.sn h₂.sn, ?_⟩
  intro n hn req hreq
  rcases ParentOwners.mem_join_nodes' hn with ⟨a, ha, hid, _⟩ | hn₂
  · rw [hid] at hreq ⊢
    exact h₁.back a ha req hreq
  · exact h₂.back n hn₂ req hreq
  · -- owners are nodes
    have side : ∀ (g : GPathM), Grown g (join g₁ g₂) → ∀ q, GownersNodes.HasNode g q →
        GownersNodes.HasNode (join g₁ g₂) q := by
      rintro g hg q ⟨m, hmm, hmid⟩
      have hs := node?_isSome_of_mem g m hmm
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n', hn', _⟩ := hg.node?_grown m.id m' hm'
      exact ⟨n', List.mem_of_find?_eq_some hn', by rw [node?_id_eq _ m.id n' hn', hmid]⟩
    intro n hn q hq
    rcases ParentOwners.mem_join_nodes' hn with ⟨a, ha, _, hown⟩ | hn₂
    · rcases hown q hq with hqa | ⟨b, hb, _, hqb⟩
      · exact side g₁ (grown_join_left g₁ g₂) q (h₁.own a ha q hqa)
      · exact side g₂ (grown_join_right g₁ g₂ hok) q (h₂.own b hb q hqb)
    · exact side g₂ (grown_join_right g₁ g₂ hok) q (h₂.own n hn₂ q hq)

theorem MInv_initSeed (hwf : WF φ) (d : NodeId) (hd : d ∈ mapNodes φ 0) :
    MInv φ (GPathM.initSeed d "") := by
  have hstep : d.step = 0 := mapNodes_step φ 0 d hd
  have hmem : ∀ n ∈ (GPathM.initSeed d "").nodes, n.id = { id := d, parent_id := none } := by
    intro n hn
    rw [initSeed_nodes] at hn
    rw [List.mem_singleton.mp hn]
  refine ⟨⟨SelfOwn.OOS_initSeed d "", SelfOwn.SNN_initSeed d "" hstep, GownersNodes.GN_initSeed d "",
      ⟨Parents.PN_initSeed d "", Parents.PBelow_initSeed d "", Parents.NotRoot_initSeed d "" hstep⟩,
      Sons.RootAtZero_initSeed d "", ParentId.PMP_initSeed d "",
      ParentId.GPMP_initSeed d "", SelfOwn.OwnBelow_initSeed d "" hstep, ?_, ?_⟩,
    Certifies.MachineOk_initSeed d "", ParentId.TL_initSeed d "" hstep,
    initSeed_ReqFiltered (reqOfCnf φ) d "" hstep (reqOfCnf_backward φ hwf d), ?_,
    NodesOnMap_initSeed φ d "" (by rw [hstep]; exact hd), Sons.SMP_initSeed d "",
    Sons.PMS_initSeed d "", Sons.SN_initSeed d "", ?_⟩
  · intro n hn
    rw [hmem n hn, initSeed_current]
    show d.step < 1
    omega
  · show (NodeIds.Ids (GPathM.initSeed d "")).Nodup
    simp only [NodeIds.Ids, initSeed_nodes]
    simp
  · intro n hn req hreq
    rw [hmem n hn] at hreq ⊢
    exact reqOfCnf_backward φ hwf d req hreq
  · intro n hn q hq
    have hn' := hn
    rw [initSeed_nodes] at hn'
    have hnq := List.mem_singleton.mp hn'
    rw [hnq] at hq
    have hq' := List.mem_singleton.mp hq
    exact ⟨n, hn, by rw [hmem n hn, hq']⟩

-- ============================================================
-- Along the driver
-- ============================================================

/-- The line invariant of `ConservationFilter`, plus `MInv` on every state. -/
def LineInv (k : Int) (line : PureLine) : Prop :=
  LineOkF φ k line ∧ ∀ kv ∈ line, MInv φ kv.2

theorem LineInv_insertPure (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineInv φ k line) (hg : StateOkF φ k (key, g)) (hm : MInv φ g) :
    LineInv φ k (insertPure line key g) := by
  refine ⟨LineOkF_insertPure φ k line key g hl.1 hg, ?_⟩
  intro kv hkv
  unfold insertPure at hkv
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    simp only [hf] at hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl.2 kv h
    · rw [List.mem_singleton.mp h]; exact hm
  | some e =>
    simp only [hf] at hkv
    obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
    cases hb : x.1 == key with
    | true =>
      have hx2 : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      have hekey : e.1 = key :=
        eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
      have hemem : e ∈ line := List.mem_of_find?_eq_some hf
      have hesok : StateOkF φ k (key, e.2) := by
        have h := hl.1.2 e hemem
        rwa [← hekey]
      have hok := okJoin_of_stateOkF φ k key e.2 g hesok hg
      show MInv φ (doJoin e.2 g)
      simp only [doJoin, hok, if_pos]
      exact MInv_join φ e.2 g hok (hl.2 e hemem) hm
    | false =>
      have hx2 : kv = x := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      exact hl.2 x hx

theorem MInv_sent (hwf : WF φ) (k : Int) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv)
    (hm : MInv φ kv.2) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    MInv φ (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval
  have hdm : d ∈ mapNodes φ (k + 1) := hsok.onMap
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hdm
  let F := filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)
  have hk : Keeps kv.2 F :=
    Keeps.trans (keeps_filterWeakAll _ _) (keeps_filterAllAgg _ _)
  have hwn := (filterWeakAll_frame (weakReqOfCnf φ d) kv.2).1
  have hsW : Sons.SMP (filterWeakAll kv.2 (weakReqOfCnf φ d)) := by
    unfold Sons.SMP; rw [hwn]; exact hm.smp
  have hnW : Parents.NotRoot (filterWeakAll kv.2 (weakReqOfCnf φ d)) := by
    unfold Parents.NotRoot; rw [hwn]; exact hm.rctx.shape.notroot
  have hvF : isValid F = true := by
    by_cases h : isValid F = true
    · exact h
    · exfalso
      have he : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = F := by
        simp only [upFilteringWeak, GPathM.up, F, if_neg h]
      rw [he] at hval
      exact h hval
  have hownF : ∀ n ∈ F.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode F q := by
    intro n hn q hq
    obtain ⟨n₀, hn₀, _, hown₀, _⟩ := hk.1.nodes_derived n hn
    obtain ⟨m, hmm, hmid⟩ := hm.own n₀ hn₀ q (hown₀ q hq)
    have hq0 : 0 ≤ q.id.step := by rw [← hmid]; exact hm.rctx.snn m hmm
    have hq1 : q.id.step < F.current_step := by
      rw [hk.1.step_eq, ← hmid]; exact hm.rctx.below m hmm
    have hRF : ReadableAgg F :=
      ⟨filterWeakAll kv.2 (weakReqOfCnf φ d), reqOfCnf φ d,
        RCtx_of_keeps (keeps_filterWeakAll _ _) hm.rctx, rfl⟩
    have rcF := RCtx_of_readableAgg F hRF
    have ctxF := Reader.Ctx_of_readable F (readable_of_readableAgg F hRF) hvF
    have hnF : F.node? n.id = some n := node?_of_mem rcF.nodup n hn
    exact rcF.gn q (ctxF.ownGow n.id n hnF q hq hq0 hq1)
  have hmF : MInv φ F :=
    MInv_of_keeps φ hk hm (AnchoredSurvive.SMP_filterAllAgg _ hsW hnW _)
      (AggInvariants.PMS_filterAllAgg _ _ (by unfold Sons.PMS; rw [hwn]; exact hm.pms))
      (AggInvariants.SN_filterAllAgg _ _ (by
        unfold Sons.SN GownersNodes.HasNode; rw [hwn]; exact hm.sn)) hownF
  have heq : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = addNode F d "" := by
    simp only [upFilteringWeak, GPathM.up, F] at hvF ⊢
    rw [if_pos hvF]
  rw [heq]
  refine MInv_addNode φ hwf F d "" ?_ (by rw [hdstep]; exact hdm) hvF
    (fun req hreq q hq hs => filterAllAgg_cleans _ _ req hreq q hq hs) hmF
  rw [hk.1.step_eq, hkv.step, hdstep]

theorem LineInv_sendToW (hwf : WF φ) (k : Int) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv)
    (hm : MInv φ kv.2) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineInv φ (k + 1) next) :
    LineInv φ (k + 1) (sendToW φ kv.2 next d) := by
  simp only [sendToW]
  split
  · next hval =>
    exact LineInv_insertPure φ (k + 1) next d _ hn
      (StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval)
      (MInv_sent φ hwf k kv hkv hm d hd hval)
  · exact hn

theorem LineInv_pureAdvanceW (hwf : WF φ) (k : Int) (line : PureLine) (hl : LineInv φ k line) :
    LineInv φ (k + 1) (pureAdvanceW φ line) := by
  simp only [pureAdvanceW]
  have hsend : ∀ kv, StateOkF φ k kv → MInv φ kv.2 → ∀ acc, LineInv φ (k + 1) acc →
      LineInv φ (k + 1) (sendAllW φ kv acc) := by
    intro kv hkv hm acc hacc
    simp only [sendAllW]
    have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
        ∀ acc, LineInv φ (k + 1) acc → LineInv φ (k + 1) (l.foldl (sendToW φ kv.2) acc) := by
      intro l
      induction l with
      | nil => intro _ acc h; exact h
      | cons x xs ih =>
        intro hx acc h
        simp only [List.foldl_cons]
        exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
          (LineInv_sendToW φ hwf k kv hkv hm x (hx x List.mem_cons_self) acc h)
    exact main _ (fun _ hd => hd) acc hacc
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkF φ k kv ∧ MInv φ kv.2) →
      ∀ acc, LineInv φ (k + 1) acc →
        LineInv φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (hsend x hx0.1 hx0.2 acc h)
  exact main line (fun kv hkv => ⟨hl.1.2 kv hkv, hl.2 kv hkv⟩) []
    ⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem LineInv_init (hwf : WF φ) : LineInv φ 0 (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineInv φ 0 acc →
        LineInv φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (LineInv_insertPure φ 0 acc x _ h (stateOkF_initSeed φ x hx0) (MInv_initSeed φ hwf x hx0))
  exact main _ (fun _ hdm => hdm) []
    ⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem LineInv_steps (hwf : WF φ) :
    ∀ (n : Nat) (k : Int) (line : PureLine), LineInv φ k line →
      LineInv φ (k + (n : Int)) (pureStepsW φ n line) := by
  intro n
  induction n with
  | zero => intro k line hl; simpa [pureStepsW] using hl
  | succ m ih =>
    intro k line hl
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    exact ih (k + 1) _ (LineInv_pureAdvanceW φ hwf k line hl)

/-- **Every state of the Improves machine's final line carries the reader's invariants**, sits at
the last step, and is valid. -/
theorem pureRunW_state (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) :
    MInv φ kv.2 ∧ kv.2.current_step = stepCount φ ∧ isValid kv.2 = true := by
  have hpos := ConservationCore.stepCount_pos φ
  have h := LineInv_steps φ hwf (stepCount φ - 1).toNat 0 (pureInit φ) (LineInv_init φ hwf)
  have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  rw [hcast] at h
  have hst := h.1.2 kv hkv
  exact ⟨h.2 kv hkv, by rw [hst.step]; omega, hst.valid⟩

-- ============================================================
-- A path through a final state is a model
-- ============================================================

theorem reqSatisfying_of_MInv (g : GPathM) (hm : MInv φ g) (sel : Int → PathNodeId)
    (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    MapChain.ReqSatisfying (reqOfCnf φ) g sel := by
  intro j hj_lo hj_hi req hreq h_req_step_pos h_req_step_lt
  have h_node_some : (g.node? (sel j)).isSome := (hchain.1 j hj_lo hj_hi).1
  let n := (g.node? (sel j)).get h_node_some
  have h_node : g.node? (sel j) = some n := by simp [n]
  have h_id_eq : n.id = sel j := node?_id_eq g (sel j) n h_node
  have hn_mem : n ∈ g.nodes := node?_mem g (sel j) h_node_some
  have hreq_n : req ∈ reqOfCnf φ n.id.id := by rw [h_id_eq]; exact hreq
  rcases int_eq_or_ne req.step j with hij | hij
  · exfalso
    have h_back := hm.back n hn_mem req hreq_n
    have h_step_eq_chain : (sel j).id.step = j := (hchain.1 j hj_lo hj_hi).2
    rw [h_id_eq, h_step_eq_chain, hij] at h_back
    omega
  · have h_owner : sel req.step ∈ GPathM.ownersAt (ownersOf g (sel j)) req.step :=
      howned (req.step) j h_req_step_pos hj_lo h_req_step_lt hj_hi hij
    have h_mem := (List.mem_filter.mp h_owner).left
    have h_step_eq : (sel req.step).id.step = req.step := by
      have h_step_bool := (List.mem_filter.mp h_owner).right
      simpa using h_step_bool
    simp only [ownersOf, h_node] at h_mem
    exact hm.rf n hn_mem req hreq_n (sel req.step) h_mem h_step_eq

/-- **A path through a state of the final line spells a model of `φ`.** -/
theorem sat_of_denot_final (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (p : List NodeId) (hp : denot kv.2 p) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := pureRunW_state φ hwf kv hkv
  obtain ⟨sel, hchain, howned, _⟩ := hp
  have hrs := reqSatisfying_of_MInv φ kv.2 hm sel hchain howned
  have hcm : ChainOnMap φ kv.2 sel := chainOnMap_of_nodesOnMap φ kv.2 hm.onMap sel hchain
  refine ⟨CnfChain.decode sel, PartialPaths.sat_of_satUpTo_final φ _ ?_⟩
  intro j c hj hle
  have hjlt : j < φ.clauses.length := by
    rcases Nat.lt_or_ge j φ.clauses.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  exact PrefixDecode.satClause_of_reqSat_prefix φ kv.2 sel hwf hchain hrs hcm j hjlt c hj
    (by rw [hstep]; omega)

-- ============================================================
-- The verdict, reduced to one pin
-- ============================================================

/-- **Soundness of the Improves verdict, reduced to the reader's one-pin obligation.** Take a state
of the final line. If one aggressive review keeps it valid, and at every state the reader visits
from there some pin keeps the graph valid, then `φ` is satisfiable. -/
theorem sat_of_pickSomeAgg (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hpick : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → PickSomeAgg g) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := pureRunW_state φ hwf kv hkv
  obtain ⟨p, hp⟩ := Inhabited_of_pickSomeAgg (filterAllAgg kv.2 []) ⟨kv.2, [], hm.rctx, rfl⟩ hv hpick
  exact sat_of_denot_final φ hwf kv hkv p
    (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p hp)

/-- info: 'AbsSat.GraphPath.Model.ReaderAggRun.pureRunW_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_state

/-- info: 'AbsSat.GraphPath.Model.ReaderAggRun.sat_of_denot_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_denot_final

/-- info: 'AbsSat.GraphPath.Model.ReaderAggRun.sat_of_pickSomeAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pickSomeAgg

end AbsSat.GraphPath.Model.ReaderAggRun
