-- lean_project/AbsSat/GraphPath/Model/ReviewJoin.lean
import AbsSat.GraphPath.Model.SendDistrib
import AbsSat.GraphPath.Model.DescentUp

/-!
# The two equations reduce to one: the review of a join

`SendDistrib` asks a whole send to distribute over a join. A send is four operations — weak filter,
pins, aggressive review, up — and three of them are no obstacle:

* **the weak filter and the pins commute with the join on the nose** (`filterWeakAll_join`,
  `foldl_filterRequire_join`): they only filter global owners, and the join's global owners are a
  union;
* **up distributes** (`embedded_addNode_join`): the up of a join sits inside the join of the ups —
  both sides add the same new node, keyed by the same map parent.

So everything is carried by the review. One statement is left, about the review alone:

* **`ReviewJoin`** — pinning and reviewing the join of two states of a line gives a state inside the
  join of the reviewed sides that stay valid (and one of them does).

From it: `sendDistrib_of_reviewJoin`, `reviewDistrib_of_reviewJoin`, and the verdict
`sat_of_reviewJoin`.
-/

namespace AbsSat.GraphPath.Model.ReviewJoin

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
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv MInv_join)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines
open AbsSat.GraphPath.Model.SendDistrib

variable (φ : Cnf)

-- ============================================================
-- The filters commute with the join
-- ============================================================

theorem filter_union (p : PathNodeId → Bool) (A B : List PathNodeId) :
    (A ++ B.filter (fun q => !A.contains q)).filter p =
      A.filter p ++ (B.filter p).filter (fun q => !(A.filter p).contains q) := by
  rw [List.filter_append, List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro q _
  cases hq : p q
  · simp
  · have hc : (A.filter p).contains q = A.contains q := by
      simp [List.mem_filter, hq]
    rw [hc]
    simp

theorem filterWeak_join (e h : GPathM) (w : Int × List NodeId) :
    filterWeak (join e h) w = join (filterWeak e w) (filterWeak h w) := by
  simp only [filterWeak, join, node?]
  rw [filter_union]

theorem filterRequire_join (e h : GPathM) (r : NodeId) :
    filterRequire (join e h) r = join (filterRequire e r) (filterRequire h r) := by
  simp only [filterRequire, join, node?]
  rw [filter_union]

theorem filterWeakAll_join (ws : List (Int × List NodeId)) :
    ∀ e h, filterWeakAll (join e h) ws = join (filterWeakAll e ws) (filterWeakAll h ws) := by
  induction ws with
  | nil => intro e h; rfl
  | cons w rest ih =>
    intro e h
    show filterWeakAll (filterWeak (join e h) w) rest = _
    rw [filterWeak_join]
    exact ih _ _

theorem foldl_filterRequire_join (rq : List NodeId) :
    ∀ e h, rq.foldl filterRequire (join e h) = join (rq.foldl filterRequire e) (rq.foldl filterRequire h) := by
  induction rq with
  | nil => intro e h; rfl
  | cons r rest ih =>
    intro e h
    show rest.foldl filterRequire (filterRequire (join e h) r) = _
    rw [filterRequire_join]
    exact ih _ _

-- ============================================================
-- Up distributes over the join
-- ============================================================

theorem isValid_addNode (g : GPathM) (d : NodeId) (t : String) (hv : isValid g = true)
    (hd : d.step = g.current_step) : isValid (addNode g d t) = true := by
  simp only [isValid, List.all_eq_true] at hv ⊢
  intro k hk
  rw [addNode_current] at hk
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  rw [addNode_gowners]
  simp only [hasStepEntry, List.any_append]
  by_cases hlt : k < g.current_step
  · have := hv k (mem_intRange h0 (by omega))
    simp only [hasStepEntry] at this
    rw [this, Bool.true_or]
  · have : (newPid g d).id.step = k := by simp only [newPid]; omega
    rw [Bool.or_eq_true]
    exact Or.inr (List.any_eq_true.mpr ⟨newPid g d, List.mem_singleton.mpr rfl, beq_iff_eq.mpr this⟩)

theorem below_join (A B : GPathM) (hcs : A.current_step = B.current_step) (hnd : NodupIds (join A B))
    (hbA : ∀ n ∈ A.nodes, n.id.id.step < A.current_step) (hbB : ∀ n ∈ B.nodes, n.id.id.step < B.current_step) :
    ∀ n ∈ (join A B).nodes, n.id.id.step < (join A B).current_step := by
  intro n hn
  have hJ : (join A B).node? n.id = some n := node?_of_mem hnd n hn
  have hcsJ : (join A B).current_step = A.current_step := rfl
  rw [hcsJ]
  rcases join_node?_source A B n.id n hJ with hA | hB
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hA
    have := hbA m (List.mem_of_find?_eq_some hm)
    rw [node?_id_eq A n.id m hm] at this
    exact this
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hB
    have := hbB m (List.mem_of_find?_eq_some hm)
    rw [node?_id_eq B n.id m hm] at this
    rw [hcs]; exact this

/-- **Up distributes over the join**: the up of a join sits inside the join of the ups. -/
theorem embedded_addNode_join (A B : GPathM) (d : NodeId) (t : String)
    (hcs : A.current_step = B.current_step) (hmp : A.map_parent = B.map_parent)
    (hd : d.step = A.current_step) (hndA : NodupIds A) (hndB : NodupIds B)
    (hbA : ∀ n ∈ A.nodes, n.id.id.step < A.current_step)
    (hbB : ∀ n ∈ B.nodes, n.id.id.step < B.current_step) :
    Embedded (addNode (join A B) d t) (join (addNode A d t) (addNode B d t)) := by
  have hndJ : NodupIds (join A B) := Reader.nodup_join A B hndA hndB
  have hpidJ : newPid (join A B) d = newPid A d := rfl
  have hpidB : newPid B d = newPid A d := by simp only [newPid, hmp]
  have hgL := grown_join_left (addNode A d t) (addNode B d t)
  -- the node of the target at `p`, from either side
  have fromA : ∀ p nA, A.node? p = some nA → ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' ∧
      (∀ q ∈ nA.owners ++ [newPid A d], q ∈ n'.owners) ∧ (∀ q ∈ nA.parents, q ∈ n'.parents) := by
    intro p nA hA
    obtain ⟨n', hn', ho, hpa, _⟩ := hgL.node?_grown p _ (addNode_node?_old A d t p nA hA)
    exact ⟨n', hn', fun q hq => ho q (by rw [upMap_owners]; exact hq),
      fun q hq => hpa q (by rw [upMap_parents]; exact hq)⟩
  have fromB : ∀ p nB, B.node? p = some nB → ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' ∧
      (∀ q ∈ nB.owners ++ [newPid A d], q ∈ n'.owners) ∧ (∀ q ∈ nB.parents, q ∈ n'.parents) := by
    intro p nB hB
    obtain ⟨n', hn', ho, hpa, _⟩ := join_node?_right (addNode A d t) (addNode B d t) p _
      (addNode_node?_old B d t p nB hB)
    refine ⟨n', hn', fun q hq => ho q ?_, fun q hq => hpa q (by rw [upMap_parents]; exact hq)⟩
    rw [upMap_owners, hpidB]; exact hq
  refine ⟨?_, ?_, ?_⟩
  · simp only [addNode_current]; rfl
  · intro p hp
    rw [addNode_gowners] at hp
    show p ∈ (addNode A d t).gowners ++ (addNode B d t).gowners.filter
      (fun q => !(addNode A d t).gowners.contains q)
    rw [addNode_gowners, addNode_gowners]
    have toA : p ∈ A.gowners ++ [newPid A d] → p ∈ (A.gowners ++ [newPid A d]) ++
        (B.gowners ++ [newPid B d]).filter (fun q => !(A.gowners ++ [newPid A d]).contains q) :=
      fun h => List.mem_append_left _ h
    rcases List.mem_append.mp hp with hp | hp
    · change p ∈ A.gowners ++ B.gowners.filter (fun q => !A.gowners.contains q) at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact toA (List.mem_append_left _ hp)
      · have hpB := (List.mem_filter.mp hp).1
        cases hc : (A.gowners ++ [newPid A d]).contains p with
        | true => exact List.mem_append_left _ (List.mem_of_elem_eq_true hc)
        | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_left _ hpB, by rw [hc]; rfl⟩)
    · rw [List.mem_singleton.mp hp, hpidJ]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  · intro p m hm
    rcases DescentUp.node_addNode_cases (join A B) d t hndJ hm with ⟨hpnew, hmeq⟩ | ⟨n0, hn0, hmeq⟩
    · -- the new node
      rw [hpidJ] at hpnew
      have hnewA := addNode_node?_new A d t hd hbA
      have hnewB := addNode_node?_new B d t (by rw [← hcs]; exact hd) hbB
      obtain ⟨n', hn', hoA, hpaA, _⟩ := hgL.node?_grown _ _ hnewA
      obtain ⟨n'', hn'', hoB, hpaB, _⟩ := join_node?_right (addNode A d t) (addNode B d t) _ _ hnewB
      rw [hpidB] at hn''
      have hsame : n'' = n' := Option.some_inj.mp (hn''.symm.trans hn')
      rw [hsame] at hoB hpaB
      refine ⟨n', by rw [hpnew]; exact hn', fun q hq _ => ?_, fun q hq _ => ?_⟩
      · rw [hmeq] at hq
        change q ∈ (join A B).gowners ++ [newPid (join A B) d] at hq
        rcases List.mem_append.mp hq with hq | hq
        · change q ∈ A.gowners ++ B.gowners.filter (fun q => !A.gowners.contains q) at hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hoA q (List.mem_append_left _ hq)
          · refine hoB q ?_
            change q ∈ B.gowners ++ [newPid B d]
            exact List.mem_append_left _ (List.mem_filter.mp hq).1
        · rw [List.mem_singleton.mp hq, hpidJ]
          exact hoA _ (List.mem_append_right _ List.mem_cons_self)
      · rw [hmeq] at hq
        change q ∈ newParents (join A B) at hq
        unfold newParents at hq
        have hcsJ : (join A B).current_step = A.current_step := rfl
        rw [hcsJ] at hq
        split at hq
        · next hpos =>
          obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hq
          have hxJ : (join A B).node? q = some x := by
            rw [← hxid]; exact node?_of_mem hndJ x (List.mem_filter.mp hx).1
          have hxs : q.id.step = A.current_step - 1 := by
            rw [← hxid]; exact eq_of_beq (List.mem_filter.mp hx).2
          rcases join_node?_source A B q x hxJ with hA | hB
          · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hA
            apply hpaA
            change q ∈ newParents A
            unfold newParents
            rw [if_pos hpos]
            exact mem_line_of_node? A q y hy _ hxs
          · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hB
            apply hpaB
            change q ∈ newParents B
            unfold newParents
            rw [← hcs, if_pos hpos]
            exact mem_line_of_node? B q y hy _ hxs
        · exact absurd hq List.not_mem_nil
    · -- an old node
      have hsrc := join_node?_source A B p n0 hn0
      obtain ⟨n', hn', hall⟩ : ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' ∧
          (∀ nA, A.node? p = some nA → (∀ q ∈ nA.owners ++ [newPid A d], q ∈ n'.owners) ∧
            (∀ q ∈ nA.parents, q ∈ n'.parents)) ∧
          (∀ nB, B.node? p = some nB → (∀ q ∈ nB.owners ++ [newPid A d], q ∈ n'.owners) ∧
            (∀ q ∈ nB.parents, q ∈ n'.parents)) := by
        rcases hsrc with hA | hB
        · obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp hA
          obtain ⟨n', hn', ho, hpa⟩ := fromA p nA hnA
          refine ⟨n', hn', fun nA' hA' => ?_, fun nB hB => ?_⟩
          · rw [hnA] at hA'
            rw [← Option.some_inj.mp hA']
            exact ⟨ho, hpa⟩
          · obtain ⟨n'', hn'', ho', hpa'⟩ := fromB p nB hB
            rw [Option.some_inj.mp (hn''.symm.trans hn')] at ho' hpa'
            exact ⟨ho', hpa'⟩
        · obtain ⟨nB, hnB⟩ := Option.isSome_iff_exists.mp hB
          obtain ⟨n', hn', ho, hpa⟩ := fromB p nB hnB
          refine ⟨n', hn', fun nA hA' => ?_, fun nB' hB' => ?_⟩
          · obtain ⟨n'', hn'', ho', hpa'⟩ := fromA p nA hA'
            rw [Option.some_inj.mp (hn''.symm.trans hn')] at ho' hpa'
            exact ⟨ho', hpa'⟩
          · rw [hnB] at hB'
            rw [← Option.some_inj.mp hB']
            exact ⟨ho, hpa⟩
      refine ⟨n', hn', fun q hq _ => ?_, fun q hq _ => ?_⟩
      · rw [hmeq, upMap_owners] at hq
        rcases List.mem_append.mp hq with hq | hq
        · rcases join_owners_source A B p n0 hn0 q hq with ⟨nA, hA, hqA⟩ | ⟨nB, hB, hqB⟩
          · exact ((hall.1 nA hA).1) q (List.mem_append_left _ hqA)
          · exact ((hall.2 nB hB).1) q (List.mem_append_left _ hqB)
        · rw [List.mem_singleton.mp hq, hpidJ]
          rcases hsrc with hA | hB
          · obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp hA
            exact ((hall.1 nA hnA).1) _ (List.mem_append_right _ List.mem_cons_self)
          · obtain ⟨nB, hnB⟩ := Option.isSome_iff_exists.mp hB
            exact ((hall.2 nB hnB).1) _ (List.mem_append_right _ List.mem_cons_self)
      · rw [hmeq, upMap_parents] at hq
        rcases join_parents_source A B p n0 hn0 q hq with ⟨nA, hA, hqA⟩ | ⟨nB, hB, hqB⟩
        · exact ((hall.1 nA hA).2) q hqA
        · exact ((hall.2 nB hB).2) q hqB

-- ============================================================
-- The one statement left
-- ============================================================

/-- The pinned state a send reviews. -/
abbrev pinned (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) : GPathM :=
  rq.foldl filterRequire (filterWeakAll g ws)

/-- **The review of a join.** Pinning and reviewing the join of two states of a line with the same key
gives a state inside the join of the reviewed sides that stay valid, and one of them does. -/
def ReviewJoin : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
    isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true →
      (isValid (reviewAgg (pinned e ws rq)) = true ∧ isValid (reviewAgg (pinned h ws rq)) = true ∧
          Embedded (reviewAgg (join (pinned e ws rq) (pinned h ws rq)))
            (join (reviewAgg (pinned e ws rq)) (reviewAgg (pinned h ws rq)))) ∨
      (isValid (reviewAgg (pinned e ws rq)) = true ∧
          Embedded (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) (reviewAgg (pinned e ws rq))) ∨
      (isValid (reviewAgg (pinned h ws rq)) = true ∧
          Embedded (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) (reviewAgg (pinned h ws rq)))

theorem reviewDistrib_of_reviewJoin (hRJ : ReviewJoin φ) : ReviewDistrib φ := by
  intro k key e h hse hsh hme hmh hv
  rcases hRJ k key e h hse hsh hme hmh [] [] hv with ⟨hve, _, _⟩ | ⟨hve, _⟩ | ⟨hvh, _⟩
  · exact Or.inl hve
  · exact Or.inl hve
  · exact Or.inr hvh

/-- The facts the up lemmas need, for a reviewed pinned state of a line state. -/
theorem reviewed_facts (k : Int) (key : NodeId) (g : GPathM) (hs : StateOkF φ k (key, g)) (hm : MInv φ g)
    (ws : List (Int × List NodeId)) (rq : List NodeId) :
    (reviewAgg (pinned g ws rq)).current_step = k + 1 ∧
    (reviewAgg (pinned g ws rq)).map_parent = some key ∧
    NodupIds (reviewAgg (pinned g ws rq)) ∧
    (∀ n ∈ (reviewAgg (pinned g ws rq)).nodes, n.id.id.step < (reviewAgg (pinned g ws rq)).current_step) ∧
    Parents.PBelow (reviewAgg (pinned g ws rq)) := by
  have hk : ReaderAgg.Keeps g (filterAllAgg (filterWeakAll g ws) rq) :=
    ReaderAgg.Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hR : ReadableAgg (filterAllAgg (filterWeakAll g ws) rq) :=
    ⟨filterWeakAll g ws, rq, ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rc := RCtx_of_readableAgg _ hR
  exact ⟨by rw [show reviewAgg (pinned g ws rq) = filterAllAgg (filterWeakAll g ws) rq from rfl,
      hk.1.step_eq, hs.step],
    by rw [show reviewAgg (pinned g ws rq) = filterAllAgg (filterWeakAll g ws) rq from rfl,
      hk.1.map_parent_eq, hs.par],
    rc.nodup, rc.below, rc.shape.pbelow⟩

/-- **`SendDistrib` from the review of a join.** -/
theorem sendDistrib_of_reviewJoin (_hwf : WF φ) (hRJ : ReviewJoin φ) : SendDistrib φ := by
  intro k key e h hse hsh hme hmh d hd hv
  let ws := weakReqOfCnf φ d
  let rq := reqOfCnf φ d
  have hok := okJoin_of_stateOkF φ k key e h hse hsh
  have hmJ := MInv_join φ e h hok hme hmh
  have hsJ : StateOkF φ k (key, join e h) := by
    have hjs := ConservationFilter.stateOkF_doJoin φ k key e h hse hsh
    unfold doJoin at hjs
    rw [if_pos hok] at hjs
    exact hjs
  have hX : filterAllAgg (filterWeakAll (join e h) ws) rq = reviewAgg (join (pinned e ws rq) (pinned h ws rq)) := by
    show reviewAgg (rq.foldl filterRequire (filterWeakAll (join e h) ws)) = _
    rw [filterWeakAll_join, foldl_filterRequire_join]
  have hsentJ : sent φ (join e h) d = up (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) d "" := by
    show up (filterAllAgg (filterWeakAll (join e h) ws) rq) d "" = _
    rw [hX]
  have hsentE : sent φ e d = up (reviewAgg (pinned e ws rq)) d "" := rfl
  have hsentH : sent φ h d = up (reviewAgg (pinned h ws rq)) d "" := rfl
  -- the facts of the three reviewed states
  obtain ⟨cX, mX, ndX, bX, pbX⟩ := reviewed_facts φ k key (join e h) hsJ hmJ ws rq
  obtain ⟨cE, mE, ndE, bE, _⟩ := reviewed_facts φ k key e hse hme ws rq
  obtain ⟨cH, mH, ndH, bH, _⟩ := reviewed_facts φ k key h hsh hmh ws rq
  have hpJ : pinned (join e h) ws rq = join (pinned e ws rq) (pinned h ws rq) := by
    show rq.foldl filterRequire (filterWeakAll (join e h) ws) = _
    rw [filterWeakAll_join, foldl_filterRequire_join]
  rw [hpJ] at cX mX ndX bX pbX
  have hkey : key ∈ mapNodes φ k := hse.onMap
  have hkstep : key.step = k := mapNodes_step φ k key hkey
  have hdstep : d.step = k + 1 := by
    have hmk : (⟨k, key.index⟩ : NodeId) ∈ mapNodes φ k := by
      have : (⟨k, key.index⟩ : NodeId) = key := by
        cases key with
        | mk sp ix => simp only at hkstep ⊢; rw [hkstep]
      rw [this]; exact hkey
    exact mapNodes_step φ (k + 1) d (mapSons_subset φ k key.index hmk d (by rw [← hkstep]; exact hd))
  -- the join's reviewed state is valid
  have hvX : isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true := by
    rw [hsentJ] at hv
    by_cases hx : isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true
    · exact hx
    · exfalso
      simp only [GPathM.up, hx] at hv
      exact hx hv
  have upv : ∀ g : GPathM, isValid g = true → up g d "" = addNode g d "" := by
    intro g hg; simp only [GPathM.up, hg, if_true]
  rw [hsentJ, hsentE, hsentH]
  rw [upv _ hvX]
  rcases hRJ k key e h hse hsh hme hmh ws rq hvX with ⟨hvE, hvH, hemb⟩ | ⟨hvE, hemb⟩ | ⟨hvH, hemb⟩
  · left
    rw [upv _ hvE, upv _ hvH]
    refine ⟨isValid_addNode _ d "" hvE (by rw [cE]; exact hdstep),
      isValid_addNode _ d "" hvH (by rw [cH]; exact hdstep), ?_⟩
    have hndG := Reader.nodup_join _ _ ndE ndH
    have hbG := below_join _ _ (cE.trans cH.symm) hndG bE bH
    have e1 := embedded_addNode _ _ d "" hemb (by rw [mX]; exact mE.symm) (by rw [cX]; exact hdstep)
      bX hbG pbX ndX
    exact embedded_trans e1 (embedded_addNode_join _ _ d "" (cE.trans cH.symm) (mE.trans mH.symm)
      (by rw [cE]; exact hdstep) ndE ndH bE bH)
  · right; left
    rw [upv _ hvE]
    refine ⟨isValid_addNode _ d "" hvE (by rw [cE]; exact hdstep), ?_⟩
    exact embedded_addNode _ _ d "" hemb (by rw [mX, mE]) (by rw [cX]; exact hdstep) bX bE pbX ndX
  · right; right
    rw [upv _ hvH]
    refine ⟨isValid_addNode _ d "" hvH (by rw [cH]; exact hdstep), ?_⟩
    exact embedded_addNode _ _ d "" hemb (by rw [mX, mH]) (by rw [cX]; exact hdstep) bX bH pbX ndX

/-- **The Improves verdict from the review of a join.** -/
theorem sat_of_reviewJoin (hwf : WF φ) (hRJ : ReviewJoin φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_distrib φ hwf (sendDistrib_of_reviewJoin φ hwf hRJ) (reviewDistrib_of_reviewJoin φ hRJ) kv hkv hv



/-- info: 'AbsSat.GraphPath.Model.ReviewJoin.sat_of_reviewJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_reviewJoin

end AbsSat.GraphPath.Model.ReviewJoin
