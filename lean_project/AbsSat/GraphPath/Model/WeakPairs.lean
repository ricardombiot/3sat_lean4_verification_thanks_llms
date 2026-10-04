-- lean_project/AbsSat/GraphPath/Model/WeakPairs.lean
import AbsSat.GraphPath.Model.SeqPin

/-!
# The run's filter, one step at a time: what is left is two pair levels

Every send of the run filters a machine state `kv.2` with weak requirements `ws` (sets of allowed map
nodes at a step) and hard ones `rq` (pins), then reviews: `filterAllAgg (filterWeakAll kv.2 ws) rq`. The
slice invariant (`FilterSlices`, v140) asks that this keep the tables exact; `GhostsLine` (v141) was the
hypothesis stated for it.

This module takes the send apart into single steps, as `SeqPin` did for pins:

* **`full_seq`** — the send sits inside, and contains, the **sequential** send: review `kv.2`, then apply
  each weak requirement with a review after it (`weakOneByOne`), then each pin with a review after it
  (`pinOneByOne`). Same fixpoint argument: each one's tables are a support carrying every requirement,
  and such a support survives any filter it satisfies (`AOk_filterWeak`, `AOk_filterAllAgg`).
* **`tablesSound_reviewAgg`** — reviewing an exact state keeps it exact (no requirement: every path
  survives).
* **`weak_node_sound`** — the node level of one weak requirement, proved as for a pin (v142).
* **`filterSlices_of_pairs`** — so the slice invariant, and with it the verdict and the complete reader,
  hold under **two pair levels**: `PairPinExact` (one pin) and `WeakPairExact` (one weak requirement),
  both on the reader's states and both only about entries between two distinct nodes.
-/

namespace AbsSat.GraphPath.Model.WeakPairs

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak filterWeakAll mem_filterWeakAll)
open AbsSat.GraphPath.Model.ConservationCore (pruned_filterWeak pruned_filterWeakAll ChainSound_filterWeak)
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk AOk_filterAllAgg SMP_filterAllAgg)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.BranchLines (embedded_refl)
open AbsSat.GraphPath.Model.BranchRun (embedded_of_pruned isValid_of_embedded)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.ReaderComplete (ReaderPinExact)
open AbsSat.GraphPath.Model.SupportSplit (embedded_of_cover)
open AbsSat.GraphPath.Model.ReaderAggRun (MInv keeps_filterWeak keeps_filterWeakAll)
open AbsSat.GraphPath.Model.SliceInvariant (FilterSlices)
open AbsSat.GraphPath.Model.SeqPin

variable {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

-- ============================================================
-- The weak filter touches only the global owners
-- ============================================================

theorem SMP_filterWeak (g : GPathM) (e : Int × List NodeId) (h : Sons.SMP g) : Sons.SMP (filterWeak g e) := h
theorem PMS_filterWeak (g : GPathM) (e : Int × List NodeId) (h : Sons.PMS g) : Sons.PMS (filterWeak g e) := h
theorem SN_filterWeak (g : GPathM) (e : Int × List NodeId) (h : Sons.SN g) : Sons.SN (filterWeak g e) := h

theorem facts_filterWeakAll : ∀ (ws : List (Int × List NodeId)) (g : GPathM), Sons.SMP g → Sons.PMS g →
    Sons.SN g → Sons.SMP (filterWeakAll g ws) ∧ Sons.PMS (filterWeakAll g ws) ∧ Sons.SN (filterWeakAll g ws) := by
  intro ws
  induction ws with
  | nil => intro g hs hp hn; exact ⟨hs, hp, hn⟩
  | cons e rest ih =>
    intro g hs hp hn
    exact ih (filterWeak g e) (SMP_filterWeak g e hs) (PMS_filterWeak g e hp) (SN_filterWeak g e hn)

/-- A support whose members satisfy a weak requirement survives it. -/
theorem AOk_filterWeak (g : GPathM) (h : AOk g S R) (e : Int × List NodeId)
    (hw : ∀ p, S p → p.id.step = e.1 → p.id ∈ e.2) : AOk (filterWeak g e) S R := by
  refine ⟨⟨?_, h.sup.node, h.sup.step, h.sup.dom, h.sup.own, h.sup.cov, h.sup.par, h.sup.son, h.sup.agg,
    h.sup.sym, h.sup.link⟩, SMP_filterWeak g e h.smp, Parents.NotRoot_of_pruned (pruned_filterWeak g e) h.nr⟩
  intro p hp
  refine List.mem_filter.mpr ⟨h.sup.gow p hp, ?_⟩
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
  by_cases hs : p.id.step = e.1
  · exact Or.inr (hw p hp hs)
  · exact Or.inl hs

theorem AOk_filterWeakAll : ∀ (ws : List (Int × List NodeId)) (g : GPathM), AOk g S R →
    (∀ e ∈ ws, ∀ p, S p → p.id.step = e.1 → p.id ∈ e.2) → AOk (filterWeakAll g ws) S R := by
  intro ws
  induction ws with
  | nil => intro g h _; exact h
  | cons e rest ih =>
    intro g h hw
    exact ih (filterWeak g e) (AOk_filterWeak g h e (hw e List.mem_cons_self))
      (fun e' he' => hw e' (List.mem_cons_of_mem _ he'))

-- ============================================================
-- Weak requirements one by one
-- ============================================================

/-- Each weak requirement, with the whole aggressive review after it. -/
def weakOneByOne (g : GPathM) (ws : List (Int × List NodeId)) : GPathM :=
  ws.foldl (fun h e => filterAllAgg (filterWeak h e) []) g

theorem pruned_weakOneByOne : ∀ (ws : List (Int × List NodeId)) (g : GPathM), Pruned g (weakOneByOne g ws) := by
  intro ws
  induction ws with
  | nil => intro g; exact Pruned.refl g
  | cons e rest ih =>
    intro g
    exact Pruned.trans (Pruned.trans (pruned_filterWeak g e) (pruned_filterAllAgg _ [])) (ih _)

theorem readableAgg_weakStep (g : GPathM) (hc : Reader.RCtx g) (e : Int × List NodeId) :
    ReadableAgg (filterAllAgg (filterWeak g e) []) :=
  ⟨filterWeak g e, [], RCtx_of_keeps (keeps_filterWeak g e) hc, rfl⟩

theorem readable_weakOneByOne : ∀ (ws : List (Int × List NodeId)) (g : GPathM), ReadableAgg g →
    ReadableAgg (weakOneByOne g ws) := by
  intro ws
  induction ws with
  | nil => intro g h; exact h
  | cons e rest ih =>
    intro g h
    exact ih _ (readableAgg_weakStep g (RCtx_of_readableAgg g h) e)

theorem facts_weakOneByOne : ∀ (ws : List (Int × List NodeId)) (g : GPathM), Reader.RCtx g → Sons.SMP g →
    Sons.PMS g → Sons.SN g → Sons.SMP (weakOneByOne g ws) ∧ Sons.PMS (weakOneByOne g ws) ∧
      Sons.SN (weakOneByOne g ws) := by
  intro ws
  induction ws with
  | nil => intro g _ hs hp hn; exact ⟨hs, hp, hn⟩
  | cons e rest ih =>
    intro g hc hs hp hn
    have hcW := RCtx_of_keeps (keeps_filterWeak g e) hc
    exact ih _ (RCtx_of_readableAgg _ (readableAgg_weakStep g hc e))
      (SMP_filterAllAgg _ (SMP_filterWeak g e hs) hcW.shape.notroot [])
      (AggInvariants.PMS_filterAllAgg _ [] (PMS_filterWeak g e hp))
      (AggInvariants.SN_filterAllAgg _ [] (SN_filterWeak g e hn))

theorem AOk_weakOneByOne : ∀ (ws : List (Int × List NodeId)) (g : GPathM), AOk g S R →
    (∀ e ∈ ws, ∀ p, S p → p.id.step = e.1 → p.id ∈ e.2) → AOk (weakOneByOne g ws) S R := by
  intro ws
  induction ws with
  | nil => intro g h _; exact h
  | cons e rest ih =>
    intro g h hw
    exact ih _ (AOk_filterAllAgg _ (AOk_filterWeak g h e (hw e List.mem_cons_self)) []
      (fun r hr => absurd hr List.not_mem_nil)) (fun e' he' => hw e' (List.mem_cons_of_mem _ he'))

/-- The global owners left by weak requirements one by one satisfy every one of them. -/
theorem gowners_weakOneByOne : ∀ (ws : List (Int × List NodeId)) (g : GPathM) (q : PathNodeId),
    q ∈ (weakOneByOne g ws).gowners → q ∈ g.gowners ∧ ∀ e ∈ ws, q.id.step = e.1 → q.id ∈ e.2 := by
  intro ws
  induction ws with
  | nil => intro g q hq; exact ⟨hq, fun e he => absurd he List.not_mem_nil⟩
  | cons e rest ih =>
    intro g q hq
    obtain ⟨h1, h2⟩ := ih _ q hq
    have h3 := (mem_filterWeakAll [e] g q).mp ((pruned_filterAllAgg (filterWeak g e) []).gowners_sub q h1)
    refine ⟨h3.1, fun e' he' hs => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he''
    · exact h3.2 e' List.mem_cons_self hs
    · exact h2 e' he'' hs

-- ============================================================
-- The send is the sequential send
-- ============================================================

/-- **The send is the sequential send.** From a machine-kind state, the send's filter
`filterAllAgg (filterWeakAll g ws) rq` and the sequential one — review, each weak requirement with a
review, each pin with a review — sit inside each other; if the first is valid, so is the second. -/
theorem full_seq (g : GPathM) (hc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) (ws : List (Int × List NodeId)) (rq : List NodeId)
    (hvA : isValid (filterAllAgg (filterWeakAll g ws) rq) = true) :
    isValid (pinOneByOne (weakOneByOne (filterAllAgg g []) ws) rq) = true ∧
    Embedded (filterAllAgg (filterWeakAll g ws) rq) (pinOneByOne (weakOneByOne (filterAllAgg g []) ws) rq) ∧
    Embedded (pinOneByOne (weakOneByOne (filterAllAgg g []) ws) rq) (filterAllAgg (filterWeakAll g ws) rq) ∧
    AdjacentOwners.Adj (filterAllAgg (filterWeakAll g ws) rq) ∧
    Sons.SMP (filterAllAgg (filterWeakAll g ws) rq) := by
  have hnr := hc.shape.notroot
  -- the send
  have hcW := RCtx_of_keeps (keeps_filterWeakAll g ws) hc
  obtain ⟨hsW, hpW, hnW⟩ := facts_filterWeakAll ws g hsmp hpms hsn
  have hRA : ReadableAgg (filterAllAgg (filterWeakAll g ws) rq) := ⟨_, rq, hcW, rfl⟩
  have hprA : Pruned g (filterAllAgg (filterWeakAll g ws) rq) :=
    Pruned.trans (pruned_filterWeakAll g ws) (pruned_filterAllAgg _ rq)
  have hsA := SMP_filterAllAgg _ hsW hcW.shape.notroot rq
  have adA := AdjacentOwners.adj_of_readable _ hRA hvA (AggInvariants.PMS_filterAllAgg _ rq hpW)
    (AggInvariants.SN_filterAllAgg _ rq hnW)
  have okA := aggOk_reviewAgg _ hvA
  -- the sequential send
  have hR0 : ReadableAgg (filterAllAgg g []) := ⟨g, [], hc, rfl⟩
  have hR1 := readable_weakOneByOne ws _ hR0
  have hRT := BranchReader.readable_pinOneByOne _ hR1 rq
  have hprT : Pruned g (pinOneByOne (weakOneByOne (filterAllAgg g []) ws) rq) :=
    Pruned.trans (pruned_filterAllAgg g [])
      (Pruned.trans (pruned_weakOneByOne ws _) (pruned_pinOneByOne rq _))
  obtain ⟨hs1, hp1, hn1⟩ := facts_weakOneByOne ws _ (RCtx_of_readableAgg _ hR0)
    (SMP_filterAllAgg g hsmp hnr []) (AggInvariants.PMS_filterAllAgg g [] hpms)
    (AggInvariants.SN_filterAllAgg g [] hsn)
  obtain ⟨_, hsT, hpT, hnT⟩ := facts_pinOneByOne rq _ (RCtx_of_readableAgg _ hR1) hs1 hp1 hn1
  have hstep := hprA.step_eq.trans hprT.step_eq.symm
  -- the send's tables survive the sequential send
  have supA := sup_of_embedded _ g adA okA hsA (embedded_of_pruned hprA hc.nodup (embedded_refl g))
  have selfA := sup_of_embedded _ _ adA okA hsA (embedded_refl _)
  have reqA : ∀ p, Mem (filterAllAgg (filterWeakAll g ws) rq) p →
      (∀ e ∈ ws, p.id.step = e.1 → p.id ∈ e.2) ∧ (∀ r ∈ rq, p.id.step = r.step → p.id = r) := by
    intro p hp
    have hg := (pruned_reviewAgg (rq.foldl filterRequire (filterWeakAll g ws))).gowners_sub p (selfA.gow p hp)
    have h1 := gowners_foldl_pin rq _ p hg
    exact ⟨((mem_filterWeakAll ws g p).mp h1.1).2, h1.2⟩
  have hAT := (AOk_pinOneByOne rq _ (AOk_weakOneByOne ws _
    (AOk_filterAllAgg g ⟨supA, hsmp, hnr⟩ [] (fun r hr => absurd hr List.not_mem_nil))
    (fun e he p hp hs => (reqA p hp).1 e he hs)) (fun r hr p hp hs => (reqA p hp).2 r hr hs)).sup
  have eAT := embedded_of_cover _ adA _ _ _ hAT hstep (fun _ _ h => h)
  have hvT := isValid_of_embedded eAT hvA
  -- the sequential send's tables survive the send
  have adT := AdjacentOwners.adj_of_readable _ hRT hvT hpT hnT
  have okT : AggFixpoint.AggOk (pinOneByOne (weakOneByOne (filterAllAgg g []) ws) rq) := by
    obtain ⟨g₀, rq₀, _, heq⟩ := hRT
    rw [heq] at hvT ⊢
    exact aggOk_reviewAgg _ hvT
  have supT := sup_of_embedded _ g adT okT hsT (embedded_of_pruned hprT hc.nodup (embedded_refl g))
  have selfT := sup_of_embedded _ _ adT okT hsT (embedded_refl _)
  have reqT : ∀ p, Mem (pinOneByOne (weakOneByOne (filterAllAgg g []) ws) rq) p →
      (∀ e ∈ ws, p.id.step = e.1 → p.id ∈ e.2) ∧ (∀ r ∈ rq, p.id.step = r.step → p.id = r) := by
    intro p hp
    have hg := selfT.gow p hp
    exact ⟨(gowners_weakOneByOne ws _ p (OraclePath.gowners_pinOneByOne_sub rq _ p hg)).2,
      fun r hr hs => OraclePath.pinned_ids rq _ r hr p hg hs⟩
  have hTA := (AOk_filterAllAgg _ (AOk_filterWeakAll ws g ⟨supT, hsmp, hnr⟩
    (fun e he p hp hs => (reqT p hp).1 e he hs)) rq (fun r hr p hp hs => (reqT p hp).2 r hr hs)).sup
  have eTA := embedded_of_cover _ adT _ _ _ hTA hstep.symm (fun _ _ h => h)
  exact ⟨hvT, eAT, eTA, adA, hsA⟩

-- ============================================================
-- Exactness step by step
-- ============================================================

/-- **Reviewing an exact state keeps it exact**: with no requirement, every path survives. -/
theorem tablesSound_reviewAgg (g : GPathM) (hnd : NodupIds g) (ht : TablesSound g) :
    TablesSound (filterAllAgg g []) := by
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  have hpr := pruned_filterAllAgg g []
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem hnd n₀ hn₀
  obtain ⟨sel, hsc, h1, h2⟩ := ht x n₀ hx₀ hx0 (by rw [← hpr.step_eq]; exact hx1) q hq0
    (by rw [← hpr.step_eq]; exact hq1) (hown q hqn)
  exact ⟨sel, ChainSound_filterAllAgg g [] sel hsc (fun r hr => absurd hr List.not_mem_nil), h1, h2⟩

/-- One weak requirement and the review keep a valid exact reader's state exact. -/
def WeakStepExact : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → TablesSound g →
    ∀ e : Int × List NodeId, isValid (filterAllAgg (filterWeak g e) []) = true →
      TablesSound (filterAllAgg (filterWeak g e) [])

theorem tablesSound_weakOneByOne (hW : WeakStepExact) : ∀ (ws : List (Int × List NodeId)) (h : GPathM),
    ReadableAgg h → isValid h = true → TablesSound h → isValid (weakOneByOne h ws) = true →
      TablesSound (weakOneByOne h ws) := by
  intro ws
  induction ws with
  | nil => intro h _ _ ht _; exact ht
  | cons e rest ih =>
    intro h hR hv ht hvS
    have hR' := readableAgg_weakStep h (RCtx_of_readableAgg h hR) e
    have hv' : isValid (filterAllAgg (filterWeak h e) []) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_weakOneByOne rest _)
        (RCtx_of_readableAgg _ hR').nodup) hvS
    exact ih _ hR' hv' (hW h hR hv ht e hv') hvS

-- ============================================================
-- The weak node level
-- ============================================================

/-- **The node level of a weak requirement.** Applying one weak requirement to a valid exact reader's
state and reviewing leaves only nodes on a surviving path: a surviving node owns something at the weak
step, that owner is one of the allowed nodes, and the state was exact. -/
theorem weak_node_sound (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true) (ht : TablesSound g)
    (e : Int × List NodeId) (hve : isValid (filterAllAgg (filterWeak g e) []) = true)
    (x : PathNodeId) (n : PNodeM) (hx : (filterAllAgg (filterWeak g e) []).node? x = some n)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < (filterAllAgg (filterWeak g e) []).current_step) :
    Realizes (filterAllAgg (filterWeak g e) []) x x := by
  have rcg := RCtx_of_readableAgg g hR
  have hRe := readableAgg_weakStep g rcg e
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRe) hve
  have ctxg := Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hv
  have hpr : Pruned g (filterAllAgg (filterWeak g e) []) :=
    Pruned.trans (pruned_filterWeak g e) (pruned_filterAllAgg _ [])
  have hcs := hpr.step_eq
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  have lift : ∀ sel, ChainSound g sel → sel x.id.step = x →
      (0 ≤ e.1 → e.1 < g.current_step → (sel e.1).id ∈ e.2) →
      Realizes (filterAllAgg (filterWeak g e) []) x x := by
    intro sel hsc hsx hin
    refine ⟨sel, ChainSound_filterAllAgg _ [] sel (ChainSound_filterWeak g e sel hsc
      (fun k h0 h1 hk => by rw [hk] at h0 h1 ⊢; exact hin h0 h1))
      (fun r hr => absurd hr List.not_mem_nil), hsx, hsx⟩
  by_cases hin : 0 ≤ e.1 ∧ e.1 < g.current_step
  · have hok := owners_ok_of_isValidNode _ n (ctxR.nodeval x n hx)
    simp only [List.all_eq_true] at hok
    have hent := hok e.1 (mem_intRange hin.1 (by rw [hcs]; omega))
    obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp hent
    have hzs' : z.id.step = e.1 := eq_of_beq hzs
    have hzg := ctxR.ownGow x n hx z hz (by omega) (by rw [hcs]; omega)
    have hzin : z.id ∈ e.2 := ((mem_filterWeakAll [e] g z).mp
      ((pruned_filterAllAgg (filterWeak g e) []).gowners_sub z hzg)).2 e List.mem_cons_self hzs'
    obtain ⟨sel, hsc, hsx, hsz⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) z (by omega) (by omega)
      (hown z hz)
    refine lift sel hsc hsx (fun _ _ => ?_)
    rw [← hzs', hsz]
    exact hzin
  · obtain ⟨sel, hsc, hsx, _⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) x hx0 (by rw [← hcs]; exact hx1)
      (ctxg.self x n₀ hx₀)
    exact lift sel hsc hsx (fun h0 h1 => absurd ⟨h0, h1⟩ hin)

/-- **The weak pair level**: every entry between two distinct nodes, after one weak requirement and the
review, lies on a surviving path. -/
def WeakPairExact : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → TablesSound g →
    ∀ e : Int × List NodeId, isValid (filterAllAgg (filterWeak g e) []) = true →
      ∀ x n, (filterAllAgg (filterWeak g e) []).node? x = some n → 0 ≤ x.id.step →
        x.id.step < (filterAllAgg (filterWeak g e) []).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (filterAllAgg (filterWeak g e) []).current_step →
          q ∈ n.owners → q ≠ x → Realizes (filterAllAgg (filterWeak g e) []) x q

theorem weakStepExact_of_pairs (h : WeakPairExact) : WeakStepExact := by
  intro g hR hv ht e hve x n hx hx0 hx1 q hq0 hq1 hqn
  by_cases hqx : q = x
  · rw [hqx]
    exact weak_node_sound g hR hv ht e hve x n hx hx0 hx1
  · exact h g hR hv ht e hve x n hx hx0 hx1 q hq0 hq1 hqn hqx

-- ============================================================
-- The slice invariant from the two pair levels
-- ============================================================

variable (φ : Cnf)

/-- **The slice invariant from single steps**: one weak requirement and one pin keep the reader's
states exact ⟹ every send of the run keeps the tables exact. -/
theorem filterSlices_of_steps (hW : WeakStepExact) (hP : ReaderPinExact) : FilterSlices φ := by
  intro k kv _ hm ht ws rq hv
  obtain ⟨hvT, eAT, eTA, adA, hsA⟩ := full_seq kv.2 hm.rctx hm.smp hm.pms hm.sn ws rq hv
  have hR0 : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have hR1 := readable_weakOneByOne ws _ hR0
  have hv1 : isValid (weakOneByOne (filterAllAgg kv.2 []) ws) = true :=
    isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_pinOneByOne rq _)
      (RCtx_of_readableAgg _ hR1).nodup) hvT
  have hv0 : isValid (filterAllAgg kv.2 []) = true :=
    isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_weakOneByOne ws _)
      (RCtx_of_readableAgg _ hR0).nodup) hv1
  have ht0 := tablesSound_reviewAgg kv.2 hm.rctx.nodup ht
  have ht1 := tablesSound_weakOneByOne hW ws _ hR0 hv0 ht0 hv1
  have htT := tablesSound_pinOneByOne hP rq _ hR1 hv1 ht1 hvT
  exact tablesSound_of_embedded eAT eTA adA hsA htT

/-- **What is left of the slice invariant is two pair levels.** -/
theorem filterSlices_of_pairs (hW : WeakPairExact) (hP : NodeLevel.PairPinExact) : FilterSlices φ :=
  filterSlices_of_steps φ (weakStepExact_of_pairs hW) (NodeLevel.readerPinExact_of_pairs hP)

/-- **The Improves verdict from the two pair levels.** -/
theorem sat_of_pairs (hwf : WF φ) (hW : WeakPairExact) (hP : NodeLevel.PairPinExact)
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  SliceInvariant.sat_of_slices φ hwf (filterSlices_of_pairs φ hW hP) kv hkv hv

/-- **On an unsatisfiable formula the machine answers UNSAT**, under the two pair levels. -/
theorem answer_unsat_of_pairs (hwf : WF φ) (hW : WeakPairExact) (hP : NodeLevel.PairPinExact)
    (hns : ¬ Satisfiable φ) : Answer.answer φ = .unsat := by
  unfold Answer.answer
  simp only
  have hall : ((PureDriverImproves.pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all
      (fun g => !isValid g) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hg
    cases hv : isValid (filterAllAgg kv.2 []) with
    | false => rfl
    | true => exact absurd (sat_of_pairs φ hwf hW hP kv hkv hv) hns
  rw [if_pos hall]

/-- **The machine always answers**, under the two pair levels. -/
theorem answer_ne_unknown_of_pairs (hwf : WF φ) (hW : WeakPairExact) (hP : NodeLevel.PairPinExact) :
    Answer.answer φ ≠ .unknown :=
  ReaderComplete.answer_ne_unknown_of_slices φ hwf (filterSlices_of_pairs φ hW hP)
    (NodeLevel.readerPinExact_of_pairs hP)

/-- info: 'AbsSat.GraphPath.Model.WeakPairs.full_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms full_seq

/-- info: 'AbsSat.GraphPath.Model.WeakPairs.sat_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pairs

/-- info: 'AbsSat.GraphPath.Model.WeakPairs.answer_ne_unknown_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_of_pairs

/-- info: 'AbsSat.GraphPath.Model.WeakPairs.answer_unsat_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_of_pairs

end AbsSat.GraphPath.Model.WeakPairs
