-- lean_project/AbsSat/GraphPath/Model/WeakNoop.lean
import AbsSat.GraphPath.Model.RunSteps
import AbsSat.GraphPath.Model.ReviewWorkImproves

/-!
# The weak requirements change nothing

The weak requirements were the author's optimization (v144 measured: identical tables with and without
them). This module proves why: at a send, what the weak filter would remove **contradicts a pin**
(`ReviewWorkImproves.idContradicts_of_weak_removed`), and in the pinned, reviewed state **no live node
contradicts a pin** — its requirements make it own the pinned node, which carries the pin's value.

* **`val`**, **`varVal_lit`** — the value a literal-step node gives its variable.
* **`lit_consistent`** — a live node at a literal step agrees with every pin on the same variable.
* **`fixes_consistent`** — so does every value a live node fixes (its own, and through its requirements).
* **`weak_member`** — every live node of the pinned, reviewed state passes the weak requirements.
* **`filterSoundAt_of_pins`** — so the send with and without the weak filter are the same state, and the
  construction invariant needs only one pin at a time (`WeakStepSoundAt` is gone).
* **`sat_of_pinPairs`** — the verdict under `PinPairSoundAt` alone.
-/

namespace AbsSat.GraphPath.Model.WeakNoop

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel mem_bounds)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.IdSeparator (varVal fixes fixesMap IdContradicts)

variable (φ : Cnf)

-- ============================================================
-- The value of a literal-step node
-- ============================================================

/-- The value a literal-step node gives its variable: its index at a variable step, the opposite at the
negation step. -/
def val (x : NodeId) : Int := if x.step % 2 = 0 then x.index else 1 - x.index

theorem varVal_lit (x : NodeId) (h0 : 0 ≤ x.step) (h1 : x.step < litBlock φ) :
    varVal φ x = some (x.step / 2, val x) := by
  unfold varVal
  rw [if_neg (by omega)]
  by_cases hev : x.step % 2 = 0
  · rw [if_pos hev]; simp [val, hev]
  · rw [if_neg hev, IdDiesProof.reqOfCnf_neg φ x h0 h1 (by omega)]
    show (if (x.step - 1) % 2 = 0 then some ((x.step - 1) / 2, 1 - x.index) else none) = _
    rw [if_pos (by omega)]
    simp only [val, hev, if_false, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, trivial⟩

-- ============================================================
-- In a pinned, reviewed state, live nodes agree with the pins
-- ============================================================

section
variable (A : GPathM) (ad : AdjacentOwners.Adj A) (hok : AggFixpoint.AggOk A) (hsmp : Sons.SMP A)
  (hrf : ReqFiltered (reqOfCnf φ) A) (rq : List NodeId)
  (hpin : ∀ q, Mem A q → ∀ r ∈ rq, q.id.step = r.step → q.id = r)

include ad hok hsmp hrf hpin in
/-- **A live node at a literal step agrees with every pin on the same variable.** -/
theorem lit_consistent (y : PathNodeId) (hy : Mem A y) (hy0 : 0 ≤ y.id.step) (hy1 : y.id.step < litBlock φ)
    (r : NodeId) (hr : r ∈ rq) (hr0 : 0 ≤ r.step) (hr1 : r.step < litBlock φ)
    (hrA : r.step < A.current_step) (hvar : y.id.step / 2 = r.step / 2) : val y.id = val r := by
  have sup := sup_self A ad hok hsmp
  by_cases hsame : y.id.step = r.step
  · rw [hpin y hy r hr hsame]
  · -- the node covers the pin's step; its owner there carries the pin
    obtain ⟨z, hyz, hzs⟩ := sup.cov y hy r.step hr0 hrA
    have hzm : Mem A z := by obtain ⟨_, _, _, h⟩ := hyz; exact h
    have hzr : z.id = r := hpin z hzm r hr hzs
    by_cases hy2 : y.id.step % 2 = 0
    · -- `y` at the variable step, the pin at its negation: the negation node owns `y`
      have hodd : r.step % 2 = 1 := by omega
      obtain ⟨mz, hmz, hyin, _⟩ := sup.sym y z hyz
      have hzid := node?_id_eq A z mz hmz
      have hreq := IdDiesProof.reqOfCnf_neg φ z.id (by rw [hzs]; exact hr0) (by rw [hzs]; exact hr1)
        (by rw [hzs]; exact hodd)
      have := hrf mz (List.mem_of_find?_eq_some hmz) _ (by rw [hzid, hreq]; exact List.mem_cons_self) y hyin
        (by show y.id.step = z.id.step - 1; rw [hzs]; omega)
      have hyi : y.id.index = 1 - z.id.index := by rw [this]
      rw [hzr] at hyi
      simp only [val, hy2, hodd, if_true, if_neg (show ¬ ((1 : Int) = 0) by decide)]
      exact hyi
    · -- `y` at the negation step, the pin at the variable: `y`'s requirement names it
      replace hy2 : y.id.step % 2 = 1 := by omega
      have hev : r.step % 2 = 0 := by omega
      obtain ⟨my, hmy, hzin, _⟩ := hyz
      have hyid := node?_id_eq A y my hmy
      have hreq := IdDiesProof.reqOfCnf_neg φ y.id hy0 hy1 hy2
      have := hrf my (List.mem_of_find?_eq_some hmy) _ (by rw [hyid, hreq]; exact List.mem_cons_self) z hzin
        (by show z.id.step = y.id.step - 1; rw [hzs]; omega)
      have hri : r.index = 1 - y.id.index := by rw [← hzr, this]
      simp only [val, hy2, hev, if_true, if_neg (show ¬ ((1 : Int) = 0) by decide)]
      omega

include ad hok hsmp hrf hpin in
/-- **Every value a live node fixes agrees with the pins**: its own value at a literal step, and at a
clause step the values its requirements name (it owns those nodes). -/
theorem fixes_consistent (hwf : WF φ) (y : PathNodeId) (hy : Mem A y)
    (hback : ∀ l ∈ reqOfCnf φ y.id, l.step < y.id.step)
    (vv : Int × Int) (hvv : vv ∈ fixesMap φ y.id)
    (r : NodeId) (hr : r ∈ rq) (hr0 : 0 ≤ r.step) (hr1 : r.step < litBlock φ) (hrA : r.step < A.current_step)
    (pv : Int × Int) (hpv : varVal φ r = some pv) (h1 : pv.1 = vv.1) : pv.2 = vv.2 := by
  have sup := sup_self A ad hok hsmp
  obtain ⟨hyb0, hyb1⟩ := mem_bounds A ad hy
  rw [varVal_lit φ r hr0 hr1] at hpv
  cases hpv
  unfold fixesMap at hvv
  by_cases hl : y.id.step < litBlock φ
  · rw [if_pos hl, varVal_lit φ y.id hyb0 hl] at hvv
    have hvv' := List.mem_singleton.mp hvv
    subst hvv'
    exact (lit_consistent φ A ad hok hsmp hrf rq hpin y hy hyb0 hl r hr hr0 hr1 hrA h1.symm).symm
  · rw [if_neg hl] at hvv
    by_cases hlb : y.id.step = litBlock φ
    · rw [if_pos hlb] at hvv; exact absurd hvv List.not_mem_nil
    · rw [if_neg hlb] at hvv
      obtain ⟨l, hlm, hlv⟩ := List.mem_filterMap.mp hvv
      have hl0 : 0 ≤ l.step := UnitPropagation.reqOfCnf_nonneg φ y.id l hlm
      have hl1 : l.step < litBlock φ := RunInhabited.reqOfCnf_lit φ hwf y.id l hlm
      rw [varVal_lit φ l hl0 hl1] at hlv
      cases hlv
      -- `y` owns a node at the requirement's step, and that node is the requirement
      obtain ⟨w, hyw, hws⟩ := sup.cov y hy l.step hl0 (by have := hback l hlm; omega)
      obtain ⟨my, hmy, hwin, hwm⟩ := hyw
      have hyid := node?_id_eq A y my hmy
      have hwl : w.id = l := hrf my (List.mem_of_find?_eq_some hmy) l (by rw [hyid]; exact hlm) w hwin hws
      have := lit_consistent φ A ad hok hsmp hrf rq hpin w hwm (by rw [hws]; exact hl0) (by rw [hws]; exact hl1)
        r hr hr0 hr1 hrA (by rw [hws]; exact h1.symm)
      rw [hwl] at this
      exact this.symm

include ad hok hsmp hrf hpin in
/-- **Every live node passes the weak requirements.** A node the weak filter would remove contradicts a
pin, through a value it or its parent fixes; but live nodes agree with every pin. -/
theorem weak_member (hwf : WF φ) (d : NodeId) (hrq : rq = reqOfCnf φ d)
    (hmap : MapReachable.NodesOnMap φ A)
    (hback : ∀ n ∈ A.nodes, ∀ l ∈ reqOfCnf φ n.id.id, l.step < n.id.id.step)
    (hrA : ∀ r ∈ rq, r.step < A.current_step)
    (p : PathNodeId) (hp : Mem A p) (e : Int × List NodeId) (he : e ∈ weakReqOfCnf φ d)
    (hs : p.id.step = e.1) : p.id ∈ e.2 := by
  by_cases hin : p.id ∈ e.2
  · exact hin
  · exfalso
    have hmapp := PinUp.onMap_of_mem φ A hmap hp
    obtain ⟨vv, hvv, r, hr, pv, hpv, h1, h2⟩ :=
      ReviewWorkImproves.idContradicts_of_weak_removed φ hwf d p e he hs hmapp hin
    have hr' : r ∈ rq := by rw [hrq]; exact hr
    have hr0 : 0 ≤ r.step := UnitPropagation.reqOfCnf_nonneg φ d r hr
    have hr1 : r.step < litBlock φ := RunInhabited.reqOfCnf_lit φ hwf d r hr
    have backOf : ∀ y, Mem A y → ∀ l ∈ reqOfCnf φ y.id, l.step < y.id.step := by
      intro y ⟨my, hmy⟩ l hl
      have hyid := node?_id_eq A y my hmy
      have := hback my (List.mem_of_find?_eq_some hmy) l (by rw [hyid]; exact hl)
      rw [hyid] at this; exact this
    unfold fixes at hvv
    rcases List.mem_append.mp hvv with hown | hpar
    · exact h2 (fixes_consistent φ A ad hok hsmp hrf rq hpin hwf p hp (backOf p hp) vv hown r hr' hr0 hr1
        (hrA r hr') pv hpv h1)
    · cases hpp : p.parent_id with
      | none => rw [hpp] at hpar; exact absurd hpar List.not_mem_nil
      | some q =>
        rw [hpp] at hpar
        obtain ⟨h0, _⟩ := mem_bounds A ad hp
        have hpos : 0 < p.id.step := by
          by_cases hz : p.id.step = 0
          · rw [PinExtends.root_of_mem A ad hp hz] at hpp; cases hpp
          · omega
        obtain ⟨v, hv, _, hpv'⟩ := PinExtends.parent_of_mem A ad hok hsmp hp hpos
        rw [hpp] at hpv'
        have hqv : q = v.id := Option.some.inj hpv'
        rw [hqv] at hpar
        exact h2 (fixes_consistent φ A ad hok hsmp hrf rq hpin hwf v hv (backOf v hv) vv hpar r hr' hr0 hr1
          (hrA r hr') pv hpv h1)

end

-- ============================================================
-- The send with and without the weak requirements
-- ============================================================

section
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll)
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.AnchoredSurvive (AOk AOk_filterAllAgg SMP_filterAllAgg)
open AbsSat.GraphPath.Model.EmbeddedSupport (sup_of_embedded Embedded)
open AbsSat.GraphPath.Model.BranchLines (embedded_refl)
open AbsSat.GraphPath.Model.BranchRun (embedded_of_pruned isValid_of_embedded)
open AbsSat.GraphPath.Model.SupportSplit (embedded_of_cover)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep FilterSoundAt soundAt_review reqOfCnf_lit)
open AbsSat.GraphPath.Model.RunSteps (PinStepSoundAt PinPairSoundAt soundAt_pinOneByOne soundAt_of_embedded
  pinStep_of_pairs)

/-- The send without the weak filter keeps the invariant. -/
def SendPinSoundAt : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → SoundAt (LitStep φ) kv.2 →
    ∀ d ∈ AbsSat.GraphMap.CnfSel.mapSons φ kv.1.step kv.1.index,
      isValid (filterAllAgg kv.2 (reqOfCnf φ d)) = true →
        SoundAt (LitStep φ) (filterAllAgg kv.2 (reqOfCnf φ d))

/-- **The weak requirements change nothing.** At a
send of the run, the pinned, reviewed state with and without the weak filter sit inside each other: each
one's tables are a support carrying the pins, and the one without the weak filter also passes the weak
requirements (`weak_member`). -/
theorem filterSoundAt_of_sends (hwf : WF φ) (hS : SendPinSoundAt φ) : FilterSoundAt φ := by
  intro k kv hkv hm ht d hd hvW
  have hnr := hm.rctx.shape.notroot
  -- the destination is one step up, and its pins are below it
  have hkey : kv.1.step = k := AbsSat.GraphMap.CnfSel.mapNodes_step φ k kv.1 hkv.onMap
  have hmk : (⟨k, kv.1.index⟩ : NodeId) ∈ mapNodes φ k := by
    have hid : (⟨k, kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix => rw [hkv1] at hkey; simp only at hkey ⊢; rw [hkey]
    rw [hid]; exact hkv.onMap
  have hd' : d ∈ mapNodes φ (k + 1) := AbsSat.GraphMap.CnfSel.mapSons_subset φ k kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = k + 1 := AbsSat.GraphMap.CnfSel.mapNodes_step φ (k + 1) d hd'
  have hlit : ∀ r ∈ reqOfCnf φ d, LitStep φ r.step := fun r hr => Or.inl (reqOfCnf_lit φ hwf d r hr)
  -- the state with the weak filter
  have hcW := RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll kv.2 (weakReqOfCnf φ d)) hm.rctx
  obtain ⟨sW, pW, nW⟩ := WeakPairs.facts_filterWeakAll (weakReqOfCnf φ d) kv.2 hm.smp hm.pms hm.sn
  have hRAw : ReadableAgg (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    ⟨_, _, hcW, rfl⟩
  have adAw := AdjacentOwners.adj_of_readable _ hRAw hvW (AggInvariants.PMS_filterAllAgg _ _ pW)
    (AggInvariants.SN_filterAllAgg _ _ nW)
  have okAw := aggOk_reviewAgg _ hvW
  have smpAw := SMP_filterAllAgg _ sW hcW.shape.notroot (reqOfCnf φ d)
  have prAw : Pruned kv.2 (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have supAw := sup_of_embedded _ kv.2 adAw okAw smpAw (embedded_of_pruned prAw hm.rctx.nodup (embedded_refl _))
  have selfAw := sup_of_embedded _ _ adAw okAw smpAw (embedded_refl _)
  have pinAw : ∀ r ∈ reqOfCnf φ d, ∀ p,
      Mem (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) p → p.id.step = r.step →
      p.id = r := by
    intro r hr p hp hs
    have hg := (pruned_reviewAgg _).gowners_sub p (selfAw.gow p hp)
    exact (SeqPin.gowners_foldl_pin (reqOfCnf φ d) _ p hg).2 r hr hs
  -- the state without it contains the one with it, and is valid
  have prA : Pruned kv.2 (filterAllAgg kv.2 (reqOfCnf φ d)) := pruned_filterAllAgg _ _
  have hstep : (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)).current_step =
      (filterAllAgg kv.2 (reqOfCnf φ d)).current_step := prAw.step_eq.trans prA.step_eq.symm
  have eAwA := embedded_of_cover _ adAw _ _ _
    (AOk_filterAllAgg kv.2 ⟨supAw, hm.smp, hnr⟩ (reqOfCnf φ d) pinAw).sup hstep (fun _ _ h => h)
  have hvA : isValid (filterAllAgg kv.2 (reqOfCnf φ d)) = true := isValid_of_embedded eAwA hvW
  -- the state without the weak filter
  have hRA : ReadableAgg (filterAllAgg kv.2 (reqOfCnf φ d)) := ⟨kv.2, _, hm.rctx, rfl⟩
  have adA := AdjacentOwners.adj_of_readable _ hRA hvA (AggInvariants.PMS_filterAllAgg _ _ hm.pms)
    (AggInvariants.SN_filterAllAgg _ _ hm.sn)
  have okA := aggOk_reviewAgg _ hvA
  have smpA := SMP_filterAllAgg _ hm.smp hnr (reqOfCnf φ d)
  have supA := sup_of_embedded _ kv.2 adA okA smpA (embedded_of_pruned prA hm.rctx.nodup (embedded_refl _))
  have selfA := sup_of_embedded _ _ adA okA smpA (embedded_refl _)
  have pinA : ∀ r ∈ reqOfCnf φ d, ∀ p, Mem (filterAllAgg kv.2 (reqOfCnf φ d)) p → p.id.step = r.step →
      p.id = r := by
    intro r hr p hp hs
    have hg := (pruned_reviewAgg _).gowners_sub p (selfA.gow p hp)
    exact (SeqPin.gowners_foldl_pin (reqOfCnf φ d) _ p hg).2 r hr hs
  have hrfA := PinUp.reqFiltered_of_pruned φ prA hm.rf
  have hmapA := MapReachable.NodesOnMap_of_pruned φ prA hm.onMap
  have hbackA : ∀ n ∈ (filterAllAgg kv.2 (reqOfCnf φ d)).nodes, ∀ l ∈ reqOfCnf φ n.id.id,
      l.step < n.id.id.step := by
    intro n hn l hl
    obtain ⟨n₀, hn₀, hid, _, _⟩ := prA.nodes_derived n hn
    rw [hid] at hl ⊢
    exact hm.back n₀ hn₀ l hl
  have hrA : ∀ r ∈ reqOfCnf φ d, r.step < (filterAllAgg kv.2 (reqOfCnf φ d)).current_step := by
    intro r hr
    have := reqOfCnf_backward φ hwf d r hr
    rw [prA.step_eq, hkv.step, ← hdstep]; exact this
  have weakA : ∀ e ∈ weakReqOfCnf φ d, ∀ p, Mem (filterAllAgg kv.2 (reqOfCnf φ d)) p → p.id.step = e.1 →
      p.id ∈ e.2 :=
    fun e he p hp hs => weak_member φ _ adA okA smpA hrfA (reqOfCnf φ d)
      (fun q hq r hr hs' => pinA r hr q hq hs') hwf d rfl hmapA hbackA hrA p hp e he hs
  have eAAw := embedded_of_cover _ adA _ _ _
    (AOk_filterAllAgg _ (WeakPairs.AOk_filterWeakAll (weakReqOfCnf φ d) kv.2 ⟨supA, hm.smp, hnr⟩ weakA)
      (reqOfCnf φ d) pinA).sup hstep.symm (fun _ _ h => h)
  exact soundAt_of_embedded _ eAwA eAAw adAw smpAw (hS k kv hkv hm ht d hd hvA)

/-- One pin at a time is enough for a send. -/
theorem sendPinSoundAt_of_pins (hwf : WF φ) (hP : PinStepSoundAt φ) : SendPinSoundAt φ := by
  intro k kv _ hm ht d _ hvA
  have hlit : ∀ r ∈ reqOfCnf φ d, LitStep φ r.step := fun r hr => Or.inl (reqOfCnf_lit φ hwf d r hr)
  obtain ⟨hvT, eAT, eTA, adA', hsA'⟩ :=
    WeakPairs.full_seq kv.2 hm.rctx hm.smp hm.pms hm.sn [] (reqOfCnf φ d) hvA
  have hR0 : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have hv0 : isValid (filterAllAgg kv.2 []) = true :=
    isValid_of_embedded (Hereditary.embedded_of_pruned_self (SeqPin.pruned_pinOneByOne _ _)
      (RCtx_of_readableAgg _ hR0).nodup) hvT
  have ht0 := soundAt_review _ kv.2 hm.rctx.nodup ht
  have htT := soundAt_pinOneByOne φ hP (reqOfCnf φ d) _ hlit hR0 hv0 ht0 hvT
  exact soundAt_of_embedded _ eAT eTA adA' hsA' htT

theorem filterSoundAt_of_pins (hwf : WF φ) (hP : PinStepSoundAt φ) : FilterSoundAt φ :=
  filterSoundAt_of_sends φ hwf (sendPinSoundAt_of_pins φ hwf hP)

/-- **The verdict by construction, from one pin at a time, towards the other literal steps.** -/
theorem sat_of_pinPairs (hwf : WF φ) (hP : PinPairSoundAt φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  RunInhabited.sat_of_soundAt φ hwf (filterSoundAt_of_pins φ hwf (pinStep_of_pairs φ hP)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.WeakNoop.sat_of_pinPairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinPairs

end

end AbsSat.GraphPath.Model.WeakNoop
