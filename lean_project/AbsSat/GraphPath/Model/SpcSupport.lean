-- lean_project/AbsSat/GraphPath/Model/SpcSupport.lean
import AbsSat.GraphPath.Model.AdjacentOwners
import AbsSat.GraphPath.Model.PinExactSome

/-!
# The support of a slice is pair consistency inside the slice

With the symmetric sweep over every step, the probe `helly rounds` (report v122) finds that the
largest support relation of a slice is reached in **one** round, and only the pair condition removes
anything: it is `Spc`, **pair consistency inside the slice** — `v` owns-entry of `x`, both in the
slice, and at every step a common owner that is also in the slice.

This module proves that the only thing to check is that `Spc` is **stable**:

* `SpcStable g mid` — for every `Spc` pair and every step, some common owner there is `Spc` with both
  ends.
* **`supported_of_spcStable`** — with the reader's invariants (`Adj`) and the author's tests
  (`AggOk`), a stable `Spc` is a support relation of the slice:
  * pairs — stability itself;
  * symmetry — owner tables are symmetric (`AggOk`);
  * parents / sons — the stable witness on the step just below (above) is an owner there, hence a
    parent (son) by `AdjacentOwners`;
  * cover — a slice member and its `mid` carrier are `Spc` (every common owner of the two owns the
    carrier, so it is in the slice), and stability on that pair gives an `Spc` owner at every step.
* **`sat_of_someSpcStable`** — the soundness of the Improves verdict when every state the reader
  visits with a choice has, at a step with a choice, a global owner whose slice has stable `Spc`.
-/

namespace AbsSat.GraphPath.Model.SpcSupport

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
open AbsSat.GraphPath.Model.AdjacentOwners
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)

/-- `z` is an owner of the node `x`. -/
def OwnedBy (g : GPathM) (x z : PathNodeId) : Prop := ∃ n, g.node? x = some n ∧ z ∈ n.owners

/-- **Pair consistency inside the slice of `mid`.** -/
def Spc (g : GPathM) (mid : NodeId) (x v : PathNodeId) : Prop :=
  Slice g mid x ∧ Slice g mid v ∧ OwnedBy g x v ∧
    ∀ l, 0 ≤ l → l < g.current_step → ∃ z, z.id.step = l ∧ Slice g mid z ∧ OwnedBy g x z ∧ OwnedBy g v z

/-- **Stability of `Spc`**: every `Spc` pair has, at every step, a common witness `Spc` with both. -/
def SpcStable (g : GPathM) (mid : NodeId) : Prop :=
  ∀ x v, Spc g mid x v → ∀ l, 0 ≤ l → l < g.current_step →
    ∃ z, z.id.step = l ∧ Spc g mid x z ∧ Spc g mid v z

theorem ownedBy_of (g : GPathM) {x z : PathNodeId} (h : OwnedBy g x z) {n : PNodeM}
    (hn : g.node? x = some n) : z ∈ n.owners := by
  obtain ⟨n', hn', hz⟩ := h
  rw [hn] at hn'
  cases hn'
  exact hz

theorem slice_bounds (g : GPathM) (a : Adj g) {mid : NodeId} {p : PathNodeId} (h : Slice g mid p) :
    0 ≤ p.id.step ∧ p.id.step < g.current_step := by
  obtain ⟨_, n, hn, _⟩ := h
  have hmem := List.mem_of_find?_eq_some hn
  rw [← node?_id_eq g p n hn]
  exact ⟨a.rc.snn n hmem, a.rc.below n hmem⟩

/-- An owner, in range, of a node is a slice member as soon as it owns a node owning a carrier… here:
a global owner whose node owns a carrier of `mid`. -/
theorem slice_of_owner (g : GPathM) (a : Adj g) (mid : NodeId) (x : PathNodeId) (n : PNodeM)
    (hx : g.node? x = some n) (z : PathNodeId) (hz : z ∈ n.owners) (h0 : 0 ≤ z.id.step)
    (h1 : z.id.step < g.current_step) (hin : ∀ m, g.node? z = some m → InSlice m mid) :
    Slice g mid z := by
  have hg := a.ctx.ownGow x n hx z hz h0 h1
  obtain ⟨m, hm, hmid⟩ := a.rc.gn z hg
  have hmz : g.node? z = some m := by rw [← hmid]; exact node?_of_mem a.rc.nodup m hm
  exact ⟨hg, m, hmz, hin m hmz⟩

/-- `Spc` is symmetric. -/
theorem spc_symm (g : GPathM) (a : Adj g) (hok : AggOk g) (mid : NodeId) (x v : PathNodeId)
    (h : Spc g mid x v) : Spc g mid v x := by
  obtain ⟨hx, hv, hxv, hw⟩ := h
  obtain ⟨_, n, hn, _⟩ := id hx
  obtain ⟨_, m, hm, _⟩ := id hv
  have hbx := slice_bounds g a hx
  have hbv := slice_bounds g a hv
  have hsym := ownSym_of_aggOk g hok x v n m hn hm hbx.1 hbx.2 hbv.1 hbv.2 (ownedBy_of g hxv hn)
    (a.ctx.nodeval x n hn) (a.ctx.nodeval v m hm)
  exact ⟨hv, hx, ⟨m, hm, hsym⟩, fun l h0 h1 => by
    obtain ⟨z, hzs, hzS, hz1, hz2⟩ := hw l h0 h1
    exact ⟨z, hzs, hzS, hz2, hz1⟩⟩

/-- **A slice member and its carrier are `Spc`.** -/
theorem spc_carrier (g : GPathM) (a : Adj g) (hok : AggOk g) (mid : NodeId)
    (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step) (x : PathNodeId) (hx : Slice g mid x) :
    ∃ q, q.id = mid ∧ Spc g mid x q := by
  obtain ⟨hxg, n, hn, q, hq, hqid⟩ := hx
  have hxS : Slice g mid x := ⟨hxg, n, hn, q, hq, hqid⟩
  have hbx := slice_bounds g a hxS
  have hq0 : 0 ≤ q.id.step := by rw [hqid]; exact h0
  have hq1 : q.id.step < g.current_step := by rw [hqid]; exact h1
  have hqg := a.ctx.ownGow x n hn q hq hq0 hq1
  obtain ⟨mq, hmq, hmqid⟩ := a.rc.gn q hqg
  have hqn : g.node? q = some mq := by rw [← hmqid]; exact node?_of_mem a.rc.nodup mq hmq
  have hqS : Slice g mid q := ⟨hqg, mq, hqn, q, a.ctx.self q mq hqn, hqid⟩
  refine ⟨q, hqid, hxS, hqS, ⟨n, hn, hq⟩, fun l hl0 hl1 => ?_⟩
  have hsh := (hok x n q mq hn hqn hbx.1 hbx.2 hq0 hq1 hq (a.ctx.nodeval x n hn)
    (a.ctx.nodeval q mq hqn)).2
  have hk := List.all_eq_true.mp hsh l (mem_intRange hl0 (by omega))
  have hent : hasStepEntry mq.owners l = true := List.all_eq_true.mp
    (owners_ok_of_isValidNode g mq (a.ctx.nodeval q mq hqn)) l (mem_intRange hl0 (by omega))
  rw [hent] at hk
  simp only [Bool.not_true, Bool.false_or] at hk
  obtain ⟨z, hz, hzq⟩ := List.any_eq_true.mp hk
  obtain ⟨hzn, hzs⟩ := List.mem_filter.mp hz
  have hzs' : z.id.step = l := eq_of_beq hzs
  have hzq' : z ∈ mq.owners := List.contains_iff_mem.mp hzq
  refine ⟨z, hzs', ?_, ⟨n, hn, hzn⟩, ⟨mq, hqn, hzq'⟩⟩
  refine slice_of_owner g a mid x n hn z hzn (by omega) (by omega) (fun mz hmz => ?_)
  -- the witness owns the carrier back
  exact ⟨q, ownSym_of_aggOk g hok q z mq mz hqn hmz hq0 hq1 (by omega) (by omega) hzq'
    (a.ctx.nodeval q mq hqn) (a.ctx.nodeval z mz hmz), hqid⟩

/-- **A stable `Spc` is a support relation of the slice.** -/
theorem supported_of_spcStable (g : GPathM) (a : Adj g) (hok : AggOk g) (mid : NodeId)
    (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step) (hst : SpcStable g mid) :
    SliceSupport.Supported g mid := by
  refine ⟨Spc g mid, fun p hp => hp.1, fun p hp => ?_, fun p hp => slice_bounds g a hp,
    fun x v h => ⟨h.1, h.2.1⟩, fun x v n h hn => ownedBy_of g h.2.2.1 hn, ?_, ?_, ?_,
    fun x v h l hl0 hl1 => ?_, fun x v h => spc_symm g a hok mid x v h⟩
  · obtain ⟨_, n, hn, _⟩ := hp
    rw [hn]; rfl
  · -- cover
    intro x hx l hl0 hl1
    obtain ⟨q, _, hxq⟩ := spc_carrier g a hok mid h0 h1 x hx
    obtain ⟨z, hzs, hxz, _⟩ := hst x q hxq l hl0 hl1
    exact ⟨z, hxz, hzs⟩
  · -- parents
    intro x d hx hd hpid v hxv
    obtain ⟨hbx0, hbx1⟩ := slice_bounds g a hx
    have hmem := List.mem_of_find?_eq_some hd
    have hid := node?_id_eq g x d hd
    have hroot : d.id.parent_id.isNone = false := by
      rw [hid]
      cases hp : x.parent_id with
      | none => exact absurd hp hpid
      | some _ => rfl
    obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _
      (SymTriReview.have_parents_of_isValidNode g d (a.ctx.nodeval x d hd) hroot)
    obtain ⟨mc0, hmc0, hmc0id⟩ := a.rc.shape.pn d hmem c0 hc0
    have hbelow := a.rc.shape.pbelow d hmem c0 hc0
    have hc0nn := a.rc.snn mc0 hmc0
    rw [hmc0id] at hc0nn
    rw [hid] at hbelow
    have hx1 : 1 ≤ x.id.step := by omega
    obtain ⟨z, hzs, hxz, hvz⟩ := hst x v hxv (x.id.step - 1) (by omega) (by omega)
    have hzd : z ∈ d.parents :=
      (owners_below_iff_parents g a x d hd hx1 z hzs).mp (ownedBy_of g hxz.2.2.1 hd)
    exact ⟨z, hzd, hxz, spc_symm g a hok mid x z hxz, spc_symm g a hok mid v z hvz⟩
  · -- sons
    intro x hx hlast v hxv
    obtain ⟨hbx0, hbx1⟩ := slice_bounds g a hx
    obtain ⟨_, n, hn, _⟩ := hx
    obtain ⟨z, hzs, hxz, hvz⟩ := hst x v hxv (x.id.step + 1) (by omega) (by omega)
    have hzson : z ∈ n.sons :=
      (owners_above_iff_sons g a x n hn (by omega) z hzs).mp (ownedBy_of g hxz.2.2.1 hn)
    obtain ⟨_, m, hm, _⟩ := hxz.2.1
    have hxp : n.id ∈ m.parents := a.pms n (List.mem_of_find?_eq_some hn) z hzson m
      (List.mem_of_find?_eq_some hm) (node?_id_eq g z m hm)
    rw [node?_id_eq g x n hn] at hxp
    exact ⟨z, m, hm, hxp, hxz, spc_symm g a hok mid x z hxz, spc_symm g a hok mid v z hvz⟩
  · -- pairs
    obtain ⟨z, hzs, hxz, hvz⟩ := hst x v h l hl0 hl1
    exact ⟨z, hxz, hvz, hzs⟩

/-- **Soundness of the Improves verdict from one stable slice per reader state.** -/
theorem sat_of_someSpcStable (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hst : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → hasChoice g = true →
      ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
        ∃ q ∈ ownersAt g.gowners k, SpcStable g q.id) :
    Satisfiable φ := by
  refine PinExactSome.sat_of_someSupported φ hwf kv hkv hv (fun g hF hvg hch => ?_)
  obtain ⟨k, hk0, hk1, hck, q, hq, hs⟩ := hst g hF hvg hch
  have a := reader_adjacent_owners φ hwf kv hkv g hF hvg
  have hok : AggOk g := by
    obtain ⟨y, reqs, hy⟩ := PinExactBoundary.readFrom_form _ ⟨kv.2, [], rfl⟩ g hF
    rw [hy] at hvg ⊢
    exact aggOk_reviewAgg _ hvg
  have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  exact ⟨k, hk0, hk1, hck, q, hq,
    supported_of_spcStable g a hok q.id (by rw [hqs]; exact hk0) (by rw [hqs]; exact hk1) hs⟩

/-- info: 'AbsSat.GraphPath.Model.SpcSupport.sat_of_someSpcStable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_someSpcStable

end AbsSat.GraphPath.Model.SpcSupport
