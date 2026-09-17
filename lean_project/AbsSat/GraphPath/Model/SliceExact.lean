-- lean_project/AbsSat/GraphPath/Model/SliceExact.lean
import AbsSat.GraphPath.Model.SliceSupport
import AbsSat.GraphPath.Model.Bridge
import AbsSat.GraphPath.Model.AggInvariants

/-!
# `Supported` is exactly `PinExact`

`SliceSupport.pinExact_of_supported` gives one direction. This module gives the other: if a valid pin
keeps the slice, the owner tables the pin leaves, restricted to the slice (`FinalRel`), are a support
relation of the slice **in the state before the pin**.

* cover — a slice member survives (`PinExact`), its node is valid, so it has an owner at every step,
  and that owner survives too, so it is in the slice (`inSlice_of_survives`);
* parents / sons — the result of `filterAllAgg` is a result of `review`, whose tables are coherent with
  the union of the parents' (sons') owners (`review_owners_coherent_parents`/`_sons`); links are owners
  (`Bridge.linksInOwners_review`), a parent lists its son (`SMP`) and a son its parent (`PMS`);
* pairs — the author's test holds on the result (`AggFixpoint.aggOk_reviewAgg`).

**`supported_iff_pinExact`**: on the reader's states, for a valid pin, `Supported g mid ↔ PinExact g mid`.
So the open obligation of v119 is neither weaker nor stronger than `PinExact`: it is the same statement
without the cascade in it.

`MInv` carries `PMS` and `SN` for this (`AggInvariants`), and `links_readFrom` transports `SMP`, `PMS`,
`SN` along the reader's states.
-/

namespace AbsSat.GraphPath.Model.SliceExact

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PinExact
open AbsSat.GraphPath.Model.AnchoredSurvive
open AbsSat.GraphPath.Model.SliceSupport
open AbsSat.GraphPath.Model.AggFixpoint

/-- The owner tables a pin of `mid` leaves, restricted to the slice. -/
def FinalRel (g : GPathM) (mid : NodeId) (x v : PathNodeId) : Prop :=
  Slice g mid x ∧ Slice g mid v ∧ ∃ n', (filterAllAgg g [mid]).node? x = some n' ∧ v ∈ n'.owners

/-- **A slice that survives its pin is supported**, by the tables the pin leaves. -/
theorem supported_of_pinExact (g : GPathM) (hR : ReadableAgg g) (hsmp : Sons.SMP g)
    (hpms : Sons.PMS g) (hsn : Sons.SN g) (mid : NodeId) (h0 : 0 ≤ mid.step)
    (hlt : mid.step < g.current_step) (hv' : isValid (filterAllAgg g [mid]) = true)
    (hpe : PinExact g mid) : SliceSupport.Supported g mid := by
  have rc := RCtx_of_readableAgg g hR
  have hR' : ReadableAgg (filterAllAgg g [mid]) := ReadableAgg_filterAllAgg g hR [mid]
  have rc' := RCtx_of_readableAgg _ hR'
  have ctx' : Pinned.Ctx (filterAllAgg g [mid]) :=
    Reader.Ctx_of_readable _ (readable_of_readableAgg _ hR') hv'
  have hpr : Pruned g (filterAllAgg g [mid]) := pruned_filterAllAgg g [mid]
  have hcs : (filterAllAgg g [mid]).current_step = g.current_step := hpr.step_eq
  have hsmp' : Sons.SMP (filterAllAgg g [mid]) := SMP_filterAllAgg g hsmp rc.shape.notroot [mid]
  have hpms' : Sons.PMS (filterAllAgg g [mid]) := AggInvariants.PMS_filterAllAgg g [mid] hpms
  have hsn' : Sons.SN (filterAllAgg g [mid]) := AggInvariants.SN_filterAllAgg g [mid] hsn
  have hagg : AggOk (filterAllAgg g [mid]) := aggOk_reviewAgg _ hv'
  obtain ⟨h, _, hform⟩ := filterAllAgg_form g rc [mid]
  have hvh : isValid (review h) = true := by rw [← hform]; exact hv'
  have hlinks : Bridge.LinksInOwners (filterAllAgg g [mid]) := by
    rw [hform]; exact Bridge.linksInOwners_review h hvh
  have cohP : ∀ k ∈ intRange 1 ((filterAllAgg g [mid]).current_step - 1),
      ∀ id ∈ ((filterAllAgg g [mid]).line k).map (·.id), ∀ d, (filterAllAgg g [mid]).node? id = some d →
        intersectOwners d.owners (unionOwnersOf (filterAllAgg g [mid]) d.parents) = d.owners := by
    rw [hform]; exact review_owners_coherent_parents h hvh
  have cohS : ∀ k ∈ intRange 0 ((filterAllAgg g [mid]).current_step - 2),
      ∀ id ∈ ((filterAllAgg g [mid]).line k).map (·.id), ∀ d, (filterAllAgg g [mid]).node? id = some d →
        intersectOwners d.owners (unionOwnersOf (filterAllAgg g [mid]) d.sons) = d.owners := by
    rw [hform]; exact review_owners_coherent_sons h hvh
  -- a node of the pinned state is a global owner there
  have gowOfNode : ∀ p m, (filterAllAgg g [mid]).node? p = some m → p ∈ (filterAllAgg g [mid]).gowners := by
    intro p m hp
    have hm := List.mem_of_find?_eq_some hp
    have hid := node?_id_eq _ p m hp
    exact (List.mem_filter.mp (Pinned.mem_ownersAt_gowners _ ctx' p m hp
      (by rw [← hid]; exact rc'.snn m hm) (by rw [← hid]; exact rc'.below m hm))).1
  -- a survivor is in the slice
  have sliceOfGow : ∀ p, p ∈ (filterAllAgg g [mid]).gowners → Slice g mid p := by
    intro p hp
    obtain ⟨m, hm, hmid⟩ := rc'.gn p hp
    obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived m hm
    have hs : n.id ∈ (filterAllAgg g [mid]).gowners := by rw [← hid, hmid]; exact hp
    refine ⟨hpr.gowners_sub p hp, n, ?_, inSlice_of_survives g rc.gn rc.nodup mid h0 hlt hv' n hn hs⟩
    rw [← hmid, hid]; exact node?_of_mem rc.nodup n hn
  have sliceOfNode : ∀ p m, (filterAllAgg g [mid]).node? p = some m → Slice g mid p :=
    fun p m hp => sliceOfGow p (gowOfNode p m hp)
  -- a slice member has a node in the pinned state
  have nodeOfSlice : ∀ p, Slice g mid p → ∃ m, (filterAllAgg g [mid]).node? p = some m := by
    rintro p ⟨_, n, hn, hin⟩
    have hmem := List.mem_of_find?_eq_some hn
    have hs := hpe n hmem hin
    rw [node?_id_eq g p n hn] at hs
    obtain ⟨m, hm, hmid⟩ := rc'.gn p hs
    exact ⟨m, by rw [← hmid]; exact node?_of_mem rc'.nodup m hm⟩
  -- a node of the pinned state comes from a node of `g`
  have derived : ∀ p m, (filterAllAgg g [mid]).node? p = some m → ∃ n, g.node? p = some n ∧
      (∀ q ∈ m.owners, q ∈ n.owners) ∧ (∀ q ∈ m.parents, q ∈ n.parents) := by
    intro p m hp
    obtain ⟨n, hn, hid, ho, hpa⟩ := hpr.nodes_derived m (List.mem_of_find?_eq_some hp)
    refine ⟨n, ?_, ho, hpa⟩
    rw [← node?_id_eq _ p m hp, hid]; exact node?_of_mem rc.nodup n hn
  have stepOfSlice : ∀ p, Slice g mid p → 0 ≤ p.id.step ∧ p.id.step < g.current_step := by
    rintro p ⟨_, n, hn, _⟩
    have hmem := List.mem_of_find?_eq_some hn
    rw [← node?_id_eq g p n hn]
    exact ⟨rc.snn n hmem, rc.below n hmem⟩
  -- an owner, in range, of a valid node: at every step
  have ownerAt : ∀ p m, (filterAllAgg g [mid]).node? p = some m → ∀ l, 0 ≤ l → l < g.current_step →
      ∃ r ∈ m.owners, r.id.step = l := by
    intro p m hp l hl0 hl1
    have hall := owners_ok_of_isValidNode _ m (ctx'.nodeval p m hp)
    have hent := List.all_eq_true.mp hall l (mem_intRange hl0 (by rw [hcs]; omega))
    obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp hent
    exact ⟨r, hr, eq_of_beq hrs⟩
  -- the owner union of neighbours that are valid nodes has an entry at every step in range
  have unionEntry : ∀ (ids : List PathNodeId) (c : PathNodeId) (mc : PNodeM), c ∈ ids →
      (filterAllAgg g [mid]).node? c = some mc → ∀ l, 0 ≤ l → l < g.current_step →
        hasStepEntry (unionOwnersOf (filterAllAgg g [mid]) ids) l = true := by
    intro ids c mc hc hmc l hl0 hl1
    obtain ⟨r, hr, hrs⟩ := ownerAt c mc hmc l hl0 hl1
    exact List.any_eq_true.mpr ⟨r, mem_unionOwnersOf _ ids c mc r hc hmc hr, beq_iff_eq.mpr hrs⟩
  -- coherence, read as membership
  have fromUnion : ∀ (ids : List PathNodeId) (os : List PathNodeId) (v : PathNodeId),
      intersectOwners os (unionOwnersOf (filterAllAgg g [mid]) ids) = os → v ∈ os →
      hasStepEntry (unionOwnersOf (filterAllAgg g [mid]) ids) v.id.step = true →
      ∃ c ∈ ids, ∃ m, (filterAllAgg g [mid]).node? c = some m ∧ v ∈ m.owners := by
    intro ids os v hcoh hv hent
    have hv' : v ∈ intersectOwners os (unionOwnersOf (filterAllAgg g [mid]) ids) := by rw [hcoh]; exact hv
    have hc := (List.mem_filter.mp hv').2
    rw [hent] at hc
    simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem] at hc
    exact FabricAdd.exists_owner_of_mem_unionOwnersOf _ ids v hc
  refine ⟨FinalRel g mid, fun p hp => hp.1, ?_, stepOfSlice, fun x v hr => ⟨hr.1, hr.2.1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- node
    rintro p ⟨_, n, hn, _⟩
    rw [hn]; rfl
  · -- own
    rintro x v n ⟨_, _, n', hn', hvm⟩ hn
    obtain ⟨n₀, hn₀, ho, _⟩ := derived x n' hn'
    rw [hn] at hn₀
    cases hn₀
    exact ho v hvm
  · -- cover
    intro x hx l hl0 hl1
    obtain ⟨n', hn'⟩ := nodeOfSlice x hx
    obtain ⟨r, hr, hrs⟩ := ownerAt x n' hn' l hl0 hl1
    have hrg := ctx'.ownGow x n' hn' r hr (by omega) (by rw [hcs]; omega)
    exact ⟨r, ⟨hx, sliceOfGow r hrg, n', hn', hr⟩, hrs⟩
  · -- parents
    intro x d hx hd hpid v hr
    obtain ⟨_, hvs, n', hn', hvm⟩ := hr
    obtain ⟨n₀, hn₀, _, hpsub⟩ := derived x n' hn'
    rw [hd] at hn₀
    cases hn₀
    have hmem' := List.mem_of_find?_eq_some hn'
    have hid' := node?_id_eq _ x n' hn'
    have hvalid := ctx'.nodeval x n' hn'
    have hroot : n'.id.parent_id.isNone = false := by
      rw [hid']
      cases hp : x.parent_id with
      | none => exact absurd hp hpid
      | some _ => rfl
    obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _ (SymTriReview.have_parents_of_isValidNode _ n' hvalid hroot)
    obtain ⟨mc0, hmc0, hmc0id⟩ := rc'.shape.pn n' hmem' c0 hc0
    have hbelow := rc'.shape.pbelow n' hmem' c0 hc0
    have hc0nn := rc'.snn mc0 hmc0
    rw [hmc0id] at hc0nn
    have hc0node : (filterAllAgg g [mid]).node? c0 = some mc0 := by
      rw [← hmc0id]; exact node?_of_mem rc'.nodup mc0 hmc0
    obtain ⟨hx0, hx1⟩ := stepOfSlice x hx
    have hk : x.id.step ∈ intRange 1 ((filterAllAgg g [mid]).current_step - 1) :=
      mem_intRange (by rw [hid'] at hbelow; omega) (by rw [hcs]; omega)
    have hcoh := cohP _ hk x (mem_line_of_node? _ x n' hn' _ rfl) n' hn'
    obtain ⟨hv0, hv1⟩ := stepOfSlice v hvs
    obtain ⟨c, hc, m', hm', hvm'⟩ := fromUnion n'.parents n'.owners v hcoh hvm
      (unionEntry n'.parents c0 mc0 hc0 hc0node _ hv0 hv1)
    have hsc := sliceOfNode c m' hm'
    have hxc : x ∈ m'.owners := by
      have hson : n'.id ∈ m'.sons :=
        hsmp' n' hmem' c hc m' (List.mem_of_find?_eq_some hm') (node?_id_eq _ c m' hm')
      rw [hid'] at hson
      exact (hlinks c m' hm').2 x hson
    exact ⟨c, hpsub c hc, ⟨hx, hsc, n', hn', (hlinks x n' hn').1 c hc⟩, ⟨hsc, hx, m', hm', hxc⟩,
      ⟨hsc, hvs, m', hm', hvm'⟩⟩
  · -- sons
    intro x hx hlast v hr
    obtain ⟨_, hvs, n', hn', hvm⟩ := hr
    have hmem' := List.mem_of_find?_eq_some hn'
    have hid' := node?_id_eq _ x n' hn'
    have hvalid := ctx'.nodeval x n' hn'
    have hnl : (n'.id.id.step == (filterAllAgg g [mid]).current_step - 1) = false := by
      rw [hid', hcs]; exact beq_false_of_ne hlast
    obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _ (SymTriReview.have_sons_of_isValidNode _ n' hvalid hnl)
    obtain ⟨mc0, hmc0, hmc0id⟩ := hsn' n' hmem' c0 hc0
    have hc0node : (filterAllAgg g [mid]).node? c0 = some mc0 := by
      rw [← hmc0id]; exact node?_of_mem rc'.nodup mc0 hmc0
    obtain ⟨hx0, hx1⟩ := stepOfSlice x hx
    have hk : x.id.step ∈ intRange 0 ((filterAllAgg g [mid]).current_step - 2) :=
      mem_intRange hx0 (by rw [hcs]; omega)
    have hcoh := cohS _ hk x (mem_line_of_node? _ x n' hn' _ rfl) n' hn'
    obtain ⟨hv0, hv1⟩ := stepOfSlice v hvs
    obtain ⟨c, hc, m', hm', hvm'⟩ := fromUnion n'.sons n'.owners v hcoh hvm
      (unionEntry n'.sons c0 mc0 hc0 hc0node _ hv0 hv1)
    have hsc := sliceOfNode c m' hm'
    have hxpar : x ∈ m'.parents := by
      have h' := hpms' n' hmem' c hc m' (List.mem_of_find?_eq_some hm') (node?_id_eq _ c m' hm')
      rwa [hid'] at h'
    obtain ⟨m, hm, _, hpsub⟩ := derived c m' hm'
    exact ⟨c, m, hm, hpsub x hxpar, ⟨hx, hsc, n', hn', (hlinks x n' hn').2 c hc⟩,
      ⟨hsc, hx, m', hm', (hlinks c m' hm').1 x hxpar⟩, ⟨hsc, hvs, m', hm', hvm'⟩⟩
  · -- pairs
    intro x v hr hx1 hx2 hv1 hv2 l hl0 hl1
    obtain ⟨hxs, hvs, n', hn', hvm⟩ := hr
    obtain ⟨nv, hnv⟩ := nodeOfSlice v hvs
    have hs := hagg x n' v nv hn' hnv hx1 (by rw [hcs]; exact hx2) hv1 (by rw [hcs]; exact hv2) hvm
      (ctx'.nodeval x n' hn') (ctx'.nodeval v nv hnv)
    have hl := List.all_eq_true.mp hs l (mem_intRange hl0 (by rw [hcs]; omega))
    obtain ⟨r0, hr0, hr0s⟩ := ownerAt v nv hnv l hl0 hl1
    have hent : hasStepEntry nv.owners l = true := List.any_eq_true.mpr ⟨r0, hr0, beq_iff_eq.mpr hr0s⟩
    rw [hent] at hl
    simp only [Bool.not_true, Bool.false_or] at hl
    obtain ⟨r, hr, hrv⟩ := List.any_eq_true.mp hl
    obtain ⟨hrx, hrs⟩ := List.mem_filter.mp hr
    have hrs' : r.id.step = l := eq_of_beq hrs
    have hrg := ctx'.ownGow x n' hn' r hrx (by omega) (by rw [hcs]; omega)
    have hsr := sliceOfGow r hrg
    exact ⟨r, ⟨hxs, hsr, n', hn', hrx⟩, ⟨hvs, hsr, nv, hnv, List.contains_iff_mem.mp hrv⟩, hrs'⟩

/-- The link invariants along the reader's states. -/
theorem links_readFrom (g₀ : GPathM) (hR₀ : ReadableAgg g₀) (hs₀ : Sons.SMP g₀) (hp₀ : Sons.PMS g₀)
    (hn₀ : Sons.SN g₀) : ∀ g, ReadFrom g₀ g → Sons.SMP g ∧ Sons.PMS g ∧ Sons.SN g := by
  intro g hF
  refine ⟨smp_readFrom g₀ hR₀ hs₀ g hF, ?_, ?_⟩
  · induction hF with
    | start => exact hp₀
    | pin g' mid _ _ ih => exact AggInvariants.PMS_filterAllAgg g' [mid] ih
  · induction hF with
    | start => exact hn₀
    | pin g' mid _ _ ih => exact AggInvariants.SN_filterAllAgg g' [mid] ih

/-- **On the reader's states, a valid pin keeps its slice exactly when the slice is supported.** -/
theorem supported_iff_pinExact (g : GPathM) (hR : ReadableAgg g) (hvg : isValid g = true)
    (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g) (mid : NodeId) (h0 : 0 ≤ mid.step)
    (hlt : mid.step < g.current_step) (hv' : isValid (filterAllAgg g [mid]) = true) :
    SliceSupport.Supported g mid ↔ PinExact g mid := by
  have rc := RCtx_of_readableAgg g hR
  refine ⟨fun hs => ?_, supported_of_pinExact g hR hsmp hpms hsn mid h0 hlt hv'⟩
  exact pinExact_of_supported g (Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hvg)
    rc.nodup rc.oos rc.snn rc.below hsmp rc.shape.notroot mid hs

/-- **Along the Improves reader, from a final state of the machine: `Supported ↔ PinExact` at every
valid pin.** -/
theorem supported_iff_pinExact_run (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ) (g : GPathM) (hF : ReadFrom (filterAllAgg kv.2 []) g)
    (hvg : isValid g = true) (mid : NodeId) (h0 : 0 ≤ mid.step) (hlt : mid.step < g.current_step)
    (hv' : isValid (filterAllAgg g [mid]) = true) :
    SliceSupport.Supported g mid ↔ PinExact g mid := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  obtain ⟨hs, hp, hn⟩ := links_readFrom _ hR₀
    (SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot [])
    (AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms) (AggInvariants.SN_filterAllAgg kv.2 [] hm.sn) g hF
  exact supported_iff_pinExact g (readableAgg_of_readFrom _ hR₀ g hF) hvg hs hp hn mid h0 hlt hv'

/-- info: 'AbsSat.GraphPath.Model.SliceExact.supported_iff_pinExact_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supported_iff_pinExact_run

end AbsSat.GraphPath.Model.SliceExact
