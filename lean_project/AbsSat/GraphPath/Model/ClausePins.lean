-- lean_project/AbsSat/GraphPath/Model/ClausePins.lean
import AbsSat.GraphPath.Model.WeakNoop

/-!
# Only the clause rows pin

A map node has three kinds of requirements (`reqOfCnf_shape`): none, one for a negation node (the
opposite value of its own variable, one step below), or three for a clause row (its three literals).

* **`soundAt_pin_top`** (no hypothesis) — a negation node pins the **top** step of the state it is sent
  from. Every node there carries the state's key (`TL`), so the pin is either the key, and no path is cut,
  or no node survives it.
* **`sendPinSoundAt_of_clauses`** — so the only pins that can cut paths are the clause rows', applied once
  every variable is built (`litBlock φ < g.current_step`): **`ClausePinSoundAt`**.
* **`sat_of_clausePins`** — the verdict under that hypothesis alone.
* **`clausePin_of_open`** (no hypothesis) — an entry one of whose ends, before the pin, owned only the pin at
  its step keeps its old path. What is left, **`ClauseOpen`**, is the entries whose two ends both still had
  another choice there; **`sat_of_clauseOpen`** is the verdict under it.
-/

namespace AbsSat.GraphPath.Model.ClausePins

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.BranchRun (isValid_of_embedded)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep soundAt_review reqOfCnf_lit)
open AbsSat.GraphPath.Model.RunSteps (PinStepSoundAt soundAt_of_embedded)
open AbsSat.GraphPath.Model.WeakNoop (SendPinSoundAt filterSoundAt_of_sends)

variable (φ : Cnf)

-- ============================================================
-- A pin at the top step cuts no path
-- ============================================================

/-- **A pin at the top step keeps the invariant.** Every node at the top carries the key, so a surviving
node's owner there shows the pin is the key, and every path already passes it. -/
theorem soundAt_pin_topL (L : Int → Prop) (k : Int) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2)
    (ht : SoundAt L kv.2) (r : NodeId) (hr : r.step = k)
    (hv : isValid (filterAllAgg kv.2 [r]) = true) : SoundAt L (filterAllAgg kv.2 [r]) := by
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  have hRr : ReadableAgg (filterAllAgg kv.2 [r]) := ⟨kv.2, [r], hm.rctx, rfl⟩
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hv
  have hpr := pruned_filterAllAgg kv.2 [r]
  have hcs := hpr.step_eq
  have htl := ParentId.TL_of_pruned hpr hm.tl
  have hk0 : 0 ≤ k := SliceInvariant.nonneg_of_mapNodes φ k kv.1 hkv.onMap
  -- the pin is the key
  have hrk : some r = some kv.1 := by
    have hok := owners_ok_of_isValidNode _ n (ctxR.nodeval x n hx)
    simp only [List.all_eq_true] at hok
    have hent := hok k (mem_intRange hk0 (by rw [hcs, hkv.step]; omega))
    obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp hent
    have hzs' : z.id.step = k := eq_of_beq hzs
    have hzg := ctxR.ownGow x n hx z hz (by omega) (by rw [hcs, hkv.step]; omega)
    have hzid : z.id = r := ReaderComplete.pin_id kv.2 r z hzg (by rw [hzs', hr])
    obtain ⟨m, hm', hmid⟩ := ctxR.gn z hzg
    have := htl m hm' (by rw [hmid, hzs', hcs, hkv.step]; omega)
    rw [hmid, hzid, hpr.map_parent_eq, hkv.par] at this
    exact this
  have hrk' : r = kv.1 := Option.some.inj hrk
  -- the entry's path in the state before the pin
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : kv.2.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem hm.rctx.nodup n₀ hn₀
  obtain ⟨sel, hsc, hsx, hsq⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) q hq0
    (by rw [← hcs]; exact hq1) hL (hown q hqn)
  refine ⟨sel, ChainSound_filterAllAgg kv.2 [r] sel hsc (fun req hreq h0 h1 => ?_), hsx, hsq⟩
  rw [List.mem_singleton.mp hreq] at h0 h1 ⊢
  obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 r.step h0 h1
  obtain ⟨m, hsm⟩ := Option.isSome_iff_exists.mp hsome
  have hmid := node?_id_eq _ _ m hsm
  have := hm.tl m (List.mem_of_find?_eq_some hsm) (by rw [hmid, hstep, hr, hkv.step]; omega)
  rw [hmid, hkv.par] at this
  rw [Option.some.inj this, hrk']

theorem soundAt_pin_top (k : Int) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2)
    (ht : SoundAt (LitStep φ) kv.2) (r : NodeId) (hr : r.step = k)
    (hv : isValid (filterAllAgg kv.2 [r]) = true) : SoundAt (LitStep φ) (filterAllAgg kv.2 [r]) :=
  soundAt_pin_topL φ (LitStep φ)  k kv hkv hm ht r hr hv

-- ============================================================
-- The clause stage
-- ============================================================

/-- **What is left**: one pin at a literal step, once every variable is built, keeps the entries towards
the other literal steps on paths. -/
def ClausePinSoundAt : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g → litBlock φ < g.current_step →
    ∀ r : NodeId, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → 0 ≤ x.id.step →
        x.id.step < (filterAllAgg g [r]).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (filterAllAgg g [r]).current_step → LitStep φ q.id.step →
          q.id.step ≠ r.step → q ∈ n.owners → Realizes (filterAllAgg g [r]) x q

/-- One clause-stage pin keeps the invariant: towards the pinned step for free, towards the others by
hypothesis. -/
theorem clauseStep (h : ClausePinSoundAt φ) (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : SoundAt (LitStep φ) g) (hlb : litBlock φ < g.current_step) (r : NodeId) (hr : LitStep φ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true) : SoundAt (LitStep φ) (filterAllAgg g [r]) := by
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  by_cases hqr : q.id.step = r.step
  · have hRr := ReadableAgg_filterAllAgg g hR [r]
    have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
    have rcg := RCtx_of_readableAgg g hR
    have hpr := pruned_filterAllAgg g [r]
    have hcs := hpr.step_eq
    obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
    have hxid := node?_id_eq _ x n hx
    have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
    have hqg := ctxR.ownGow x n hx q hqn hq0 hq1
    have hqid : q.id = r := ReaderComplete.pin_id g r q hqg hqr
    obtain ⟨sel, hsc, hsx, hsq⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) q hq0
      (by rw [← hcs]; exact hq1) hL (hown q hqn)
    refine ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => ?_), hsx, hsq⟩
    rw [List.mem_singleton.mp hreq, ← hqr, hsq, hqid]
  · exact h g hR hv ht hlb r hr hvr x n hx hx0 hx1 q hq0 hq1 hL hqr hqn

theorem soundAt_clausePins (hC : ClausePinSoundAt φ) : ∀ (rs : List NodeId) (h : GPathM),
    (∀ r ∈ rs, LitStep φ r.step) → ReadableAgg h → isValid h = true → SoundAt (LitStep φ) h →
      litBlock φ < h.current_step → isValid (pinOneByOne h rs) = true →
        SoundAt (LitStep φ) (pinOneByOne h rs) := by
  intro rs
  induction rs with
  | nil => intro h _ _ _ ht _ _; exact ht
  | cons q rest ih =>
    intro h hl hR hv ht hlb hvS
    have hR' := ReadableAgg_filterAllAgg h hR [q]
    have hv' : isValid (filterAllAgg h [q]) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (SeqPin.pruned_pinOneByOne rest _)
        (RCtx_of_readableAgg _ hR').nodup) hvS
    exact ih _ (fun r hr => hl r (List.mem_cons_of_mem _ hr)) hR' hv'
      (clauseStep φ hC h hR hv ht hlb q (hl q List.mem_cons_self) hv')
      (by rw [(pruned_filterAllAgg h [q]).step_eq]; exact hlb) hvS

-- ============================================================
-- The send
-- ============================================================

/-- **A send keeps the invariant, given the clause stage.** No requirement: the review. A negation node:
the top step (`soundAt_pin_top`). A clause row: its pins, one at a time, all variables built. -/
theorem sendPinSoundAt_of_clauses (hwf : WF φ) (hC : ClausePinSoundAt φ) : SendPinSoundAt φ := by
  intro k kv hkv hm ht d hd hvA
  have hkey : kv.1.step = k := AbsSat.GraphMap.CnfSel.mapNodes_step φ k kv.1 hkv.onMap
  have hmk : (⟨k, kv.1.index⟩ : NodeId) ∈ mapNodes φ k := by
    have hid : (⟨k, kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix => rw [hkv1] at hkey; simp only at hkey ⊢; rw [hkey]
    rw [hid]; exact hkv.onMap
  have hd' : d ∈ mapNodes φ (k + 1) :=
    AbsSat.GraphMap.CnfSel.mapSons_subset φ k kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = k + 1 := AbsSat.GraphMap.CnfSel.mapNodes_step φ (k + 1) d hd'
  rcases reqOfCnf_shape φ d with h | h | ⟨c, _, hlb, _⟩
  · rw [h] at hvA ⊢; exact soundAt_review _ kv.2 hm.rctx.nodup ht
  · rw [h] at hvA ⊢
    exact soundAt_pin_top φ k kv hkv hm ht _ (by show d.step - 1 = k; omega) hvA
  · have hlit : ∀ r ∈ reqOfCnf φ d, LitStep φ r.step := fun r hr => Or.inl (reqOfCnf_lit φ hwf d r hr)
    obtain ⟨hvT, eAT, eTA, adA, hsA⟩ :=
      WeakPairs.full_seq kv.2 hm.rctx hm.smp hm.pms hm.sn [] (reqOfCnf φ d) hvA
    have hR0 : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
    have hv0 : isValid (filterAllAgg kv.2 []) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (SeqPin.pruned_pinOneByOne _ _)
        (RCtx_of_readableAgg _ hR0).nodup) hvT
    have ht0 := soundAt_review _ kv.2 hm.rctx.nodup ht
    have hlb0 : litBlock φ < (filterAllAgg kv.2 []).current_step := by
      rw [(pruned_filterAllAgg kv.2 []).step_eq, hkv.step, ← hdstep]; exact hlb
    have htT := soundAt_clausePins φ hC (reqOfCnf φ d) _ hlit hR0 hv0 ht0 hlb0 hvT
    exact soundAt_of_embedded _ eAT eTA adA hsA htT

/-- **The verdict by construction, from the clause stage alone.** -/
theorem sat_of_clausePins (hwf : WF φ) (hC : ClausePinSoundAt φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  RunInhabited.sat_of_soundAt φ hwf (filterSoundAt_of_sends φ hwf (sendPinSoundAt_of_clauses φ hwf hC)) kv
    hkv hv

/-- info: 'AbsSat.GraphPath.Model.ClausePins.sat_of_clausePins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_clausePins

-- ============================================================
-- An end that already decides the pinned step
-- ============================================================

/-- A path through `y` passes, at every other step, a node `y` owns; so if `y` owns only the pin there,
the path passes the pin. -/
theorem through_pin (g : GPathM) (sel : Int → PathNodeId) (hsc : ChainSound g sel) (y : PathNodeId)
    (hy : sel y.id.step = y) (hy0 : 0 ≤ y.id.step) (hy1 : y.id.step < g.current_step) (m₀ : PNodeM)
    (hm : g.node? y = some m₀) (r : NodeId) (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step)
    (hne : r.step ≠ y.id.step) (hdec : ∀ w ∈ m₀.owners, w.id.step = r.step → w.id = r) :
    (sel r.step).id = r := by
  have h := hsc.chain.2.1 r.step y.id.step hr0 hy0 hr1 hy1 hne
  have hown : ownersOf g (sel y.id.step) = m₀.owners := by rw [hy]; simp only [ownersOf, hm]
  rw [hown] at h
  obtain ⟨hmem, hs⟩ := List.mem_filter.mp h
  exact hdec _ hmem (eq_of_beq hs)

/-- **The core**: the clause-stage pin, for an entry whose two ends each still had another choice at the
pinned step before the pin. -/
def ClauseOpen : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g → litBlock φ < g.current_step →
    ∀ r : NodeId, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → 0 ≤ x.id.step →
        x.id.step < (filterAllAgg g [r]).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (filterAllAgg g [r]).current_step → LitStep φ q.id.step →
          q.id.step ≠ r.step → q ∈ n.owners →
          (∀ n₀, g.node? x = some n₀ → ∃ w ∈ n₀.owners, w.id.step = r.step ∧ w.id ≠ r) →
          (∀ m₀, g.node? q = some m₀ → ∃ w ∈ m₀.owners, w.id.step = r.step ∧ w.id ≠ r) →
          Realizes (filterAllAgg g [r]) x q

/-- **An end that decides the pinned step is free.** If, before the pin, `x` or `q` owned only the pin at
its step, the entry's old path already passes the pin and survives it. -/
theorem clausePin_of_open (hO : ClauseOpen φ) : ClausePinSoundAt φ := by
  intro g hR hv ht hlb r hr hvr x n hx hx0 hx1 q hq0 hq1 hL hqr hqn
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have rcg := RCtx_of_readableAgg g hR
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  -- the two ends before the pin
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  have hqg := ctxR.ownGow x n hx q hqn hq0 hq1
  obtain ⟨mq, hmq, hmqid⟩ := ctxR.gn q hqg
  obtain ⟨m₀, hm₀, hid', _, _⟩ := hpr.nodes_derived mq hmq
  have hq₀ : g.node? q = some m₀ := by rw [← hmqid, hid']; exact node?_of_mem rcg.nodup m₀ hm₀
  -- the old path, and when it survives
  have survive : ∀ sel, ChainSound g sel → sel x.id.step = x → sel q.id.step = q →
      (∀ h0 : 0 ≤ r.step, ∀ h1 : r.step < g.current_step, (sel r.step).id = r) →
      Realizes (filterAllAgg g [r]) x q := by
    intro sel hsc hsx hsq hpass
    exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq h0 h1 => by
      rw [List.mem_singleton.mp hreq] at h0 h1 ⊢; exact hpass h0 h1), hsx, hsq⟩
  obtain ⟨sel, hsc, hsx, hsq⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) q hq0
    (by rw [← hcs]; exact hq1) hL (hown q hqn)
  by_cases hux : ∃ w ∈ n₀.owners, w.id.step = r.step ∧ w.id ≠ r
  · by_cases huq : ∃ w ∈ m₀.owners, w.id.step = r.step ∧ w.id ≠ r
    · exact hO g hR hv ht hlb r hr hvr x n hx hx0 hx1 q hq0 hq1 hL hqr hqn
        (fun n' h => by rw [hx₀] at h; cases h; exact hux)
        (fun m' h => by rw [hq₀] at h; cases h; exact huq)
    · -- `q` decides the pinned step
      refine survive sel hsc hsx hsq (fun h0 h1 => through_pin g sel hsc q hsq hq0
        (by rw [← hcs]; exact hq1) m₀ hq₀ r h0 h1 (fun h => hqr h.symm) (fun w hw hws => ?_))
      exact Decidable.byContradiction fun hne => huq ⟨w, hw, hws, hne⟩
  · -- `x` decides the pinned step
    refine survive sel hsc hsx hsq (fun h0 h1 => ?_)
    by_cases hxr : r.step = x.id.step
    · have hxg := ctxR.ownGow x n hx x (ctxR.self x n hx) hx0 hx1
      rw [hxr, hsx]
      exact ReaderComplete.pin_id g r x hxg hxr.symm
    · exact through_pin g sel hsc x hsx hx0 (by rw [← hcs]; exact hx1) n₀ hx₀ r h0 h1 hxr
        (fun w hw hws => Decidable.byContradiction fun hne => hux ⟨w, hw, hws, hne⟩)

/-- **The verdict by construction, from the open core alone.** -/
theorem sat_of_clauseOpen (hwf : WF φ) (hO : ClauseOpen φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  sat_of_clausePins φ hwf (clausePin_of_open φ hO) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.ClausePins.sat_of_clauseOpen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_clauseOpen

end AbsSat.GraphPath.Model.ClausePins
