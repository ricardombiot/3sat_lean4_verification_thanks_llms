-- lean/improves_bin/AbsSatBin/GraphPath/Model/KernelSplit.lean
import AbsSatBin.GraphPath.Model.KernelReader

/-!
# `KernelSplit ⇐ TriPin`: the sub-kernel of a pin

Let `x` be a live node of a kernel `g`. Its **sub-kernel** (`restrictPin g x`) keeps the nodes whose
table holds `x`, and cuts every table and every link down to them.

* **`TriPin g x`**: two nodes that own each other and both own `x` share, at every step, an entry that
  `x`'s table also holds. It is the pair rule with the pin as a fixed third member (v191, proposal B),
  and it asks nothing about triples without `x`.
* **`restrict_kernel`**: under `TriPin g x`, the sub-kernel is a valid kernel below `g` whose global
  owners at `x`'s step are only `x`. So **pinning `x` survives** (`pin_survives_of_triPin`).

Why each clause of `Kernel` holds on the sub-kernel:
* entries at every step and the pair rule: `TriPin` (and the pair rule of `g` against `x` itself);
* a table entry `v` of `y` at the step just below (above) `y` is a parent (son) of `y`: the kernel's
  neighbour clause names a parent carrying `v`, and at the parent's own step its table is itself
  (`OOS`). So the neighbour clause of the sub-kernel comes from `TriPin` at the adjacent step;
* the links and the global owners are cut down to the same set, and symmetry is untouched.

With the reader: **`KernelSplit` holds as soon as, at every valid state the reader visits, some node of
the first choice satisfies `TriPin`** (`kernelSplit_of_triPin`, `readerVerdictW_iff_of_triPin`).
-/

namespace AbsSatBin.GraphPath.Model.KernelSplit

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelReader
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- The pair rule with the pin as a fixed third member. -/
def TriPin (g : GPathM) (x : PathNodeId) : Prop :=
  ∀ y ny w nw nx, g.node? y = some ny → g.node? w = some nw → g.node? x = some nx →
    x ∈ ny.owners → x ∈ nw.owners → w ∈ ny.owners →
    ∀ l, 0 ≤ l → l < g.current_step → ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l

/-- What the construction reads from the state besides the kernel. -/
structure PinCtx (g : GPathM) : Prop where
  ker   : Kernel g
  nd    : NodupIds g
  oos   : SelfOwn.OOS g
  pb    : Parents.PBelow g
  sa    : Sons.SAbove g
  snn   : SelfOwn.SNN g
  below : ∀ n ∈ g.nodes, n.id.id.step < g.current_step

-- ============================================================
-- The sub-kernel
-- ============================================================

/-- `v` is a node whose table holds `x`. -/
def inS (g : GPathM) (x v : PathNodeId) : Bool :=
  match g.node? v with
  | some nv => nv.owners.contains x
  | none => false

theorem inS_of {g : GPathM} {x v : PathNodeId} {nv : PNodeM} (hn : g.node? v = some nv)
    (hx : x ∈ nv.owners) : inS g x v = true := by
  unfold inS; rw [hn]; exact List.elem_eq_true_of_mem hx

theorem of_inS {g : GPathM} {x v : PathNodeId} (h : inS g x v = true) :
    ∃ nv, g.node? v = some nv ∧ x ∈ nv.owners := by
  unfold inS at h
  cases hn : g.node? v with
  | none => rw [hn] at h; cases h
  | some nv => rw [hn] at h; exact ⟨nv, rfl, List.mem_of_elem_eq_true h⟩

/-- A node cut down to the sub-kernel. -/
def rn (g : GPathM) (x : PathNodeId) (n : PNodeM) : PNodeM :=
  { n with owners := n.owners.filter (inS g x), parents := n.parents.filter (inS g x),
           sons := n.sons.filter (inS g x) }

/-- **The sub-kernel of `x`**: the nodes whose table holds `x`, everything cut down to them. -/
def restrictPin (g : GPathM) (x : PathNodeId) : GPathM :=
  { nodes := (g.nodes.filter (fun n => n.owners.contains x)).map (rn g x),
    gowners := g.gowners.filter (inS g x),
    current_step := g.current_step,
    map_parent := g.map_parent }

section
variable {g : GPathM} {x : PathNodeId}

theorem nodup_restrict (hnd : NodupIds g) : NodupIds (restrictPin g x) := by
  unfold NodupIds at hnd ⊢
  show (((g.nodes.filter (fun n => n.owners.contains x)).map (rn g x)).map (·.id)).Nodup
  rw [List.map_map]
  have he : ((·.id) ∘ rn g x) = (fun n : PNodeM => n.id) := rfl
  rw [he]
  exact List.Sublist.nodup (List.Sublist.map _ List.filter_sublist) hnd

theorem restrict_node?_inv (hnd : NodupIds g) (p : PathNodeId) (m : PNodeM)
    (h : (restrictPin g x).node? p = some m) :
    ∃ n, g.node? p = some n ∧ x ∈ n.owners ∧ m = rn g x n := by
  have hm := List.mem_of_find?_eq_some h
  have hid := node?_id_eq _ p m h
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hng, hc⟩ := List.mem_filter.mp hn
  have hnid : n.id = p := hid
  exact ⟨n, by rw [← hnid]; exact node?_of_mem hnd n hng, List.mem_of_elem_eq_true hc, rfl⟩

theorem restrict_node? (hnd : NodupIds g) (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n)
    (hx : x ∈ n.owners) : (restrictPin g x).node? p = some (rn g x n) := by
  have hmem : rn g x n ∈ (restrictPin g x).nodes :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hn,
      List.elem_eq_true_of_mem hx⟩)
  have := node?_of_mem (nodup_restrict (x := x) hnd) _ hmem
  have hid : (rn g x n).id = p := node?_id_eq g p n hn
  rw [hid] at this
  exact this
end

-- ============================================================
-- Owners at the adjacent steps are the neighbours
-- ============================================================

theorem parent_of_owner {g : GPathM} (c : PinCtx g) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (h1 : 1 ≤ y.id.step) (r : PathNodeId) (hr : r ∈ ny.owners)
    (hrs : r.id.step = y.id.step - 1) : r ∈ ny.parents ∧ ∃ nr, g.node? r = some nr := by
  obtain ⟨cc, hcc, nc, hnc, hrc⟩ := c.ker.nbrP y ny hy h1 r hr
  have hyid : ny.id = y := node?_id_eq g y ny hy
  have hcs : cc.id.step = y.id.step - 1 := by
    have := c.pb ny (List.mem_of_find?_eq_some hy) cc hcc; rw [hyid] at this; exact this
  have hncid : nc.id = cc := node?_id_eq g cc nc hnc
  have he : r = nc.id := c.oos nc (List.mem_of_find?_eq_some hnc) r hrc (by rw [hncid, hrs, hcs])
  rw [hncid] at he
  subst he
  exact ⟨hcc, nc, hnc⟩

theorem son_of_owner {g : GPathM} (c : PinCtx g) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (h1 : y.id.step ≤ g.current_step - 2) (r : PathNodeId)
    (hr : r ∈ ny.owners) (hrs : r.id.step = y.id.step + 1) : r ∈ ny.sons ∧ ∃ nr, g.node? r = some nr := by
  obtain ⟨cc, hcc, nc, hnc, hrc⟩ := c.ker.nbrS y ny hy h1 r hr
  have hyid : ny.id = y := node?_id_eq g y ny hy
  have hcs : cc.id.step = y.id.step + 1 := by
    have := c.sa ny (List.mem_of_find?_eq_some hy) cc hcc; rw [hyid] at this; exact this
  have hncid : nc.id = cc := node?_id_eq g cc nc hnc
  have he : r = nc.id := c.oos nc (List.mem_of_find?_eq_some hnc) r hrc (by rw [hncid, hrs, hcs])
  rw [hncid] at he
  subst he
  exact ⟨hcc, nc, hnc⟩

-- ============================================================
-- The sub-kernel is a valid kernel below the state
-- ============================================================

theorem restrict_kernel {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (ht : TriPin g x) :
    Kernel (restrictPin g x) ∧ isValid (restrictPin g x) = true ∧ Below g (restrictPin g x) ∧
      ∀ z ∈ (restrictPin g x).gowners, z.id.step = x.id.step → z.id = x.id := by
  have hk := c.ker
  -- an entry of `x`'s table is in the set
  have hxo : ∀ r ∈ nx.owners, inS g x r = true := by
    intro r hr
    obtain ⟨nr, hnr⟩ := hk.isNode_owner x nx hx r hr
    exact inS_of hnr (hk.sym x nx r nr hx hnr hr)
  have hcs : (restrictPin g x).current_step = g.current_step := rfl
  -- the neighbour clause of the sub-kernel, from `TriPin` at the adjacent step
  have hnbP : ∀ y ny, g.node? y = some ny → x ∈ ny.owners → 1 ≤ y.id.step →
      ∀ v nv, g.node? v = some nv → x ∈ nv.owners → v ∈ ny.owners →
      ∃ r ∈ ny.parents, ∃ nr, g.node? r = some nr ∧ inS g x r = true ∧ v ∈ nr.owners := by
    intro y ny hy hxy h1 v nv hv hxv hvy
    have hlt : y.id.step - 1 < g.current_step := by
      have := c.below ny (List.mem_of_find?_eq_some hy); rw [node?_id_eq g y ny hy] at this; omega
    obtain ⟨r, hr, hrv, hrx, hrs⟩ := ht y ny v nv nx hy hv hx hxy hxv hvy (y.id.step - 1) (by omega) hlt
    obtain ⟨hpar, nr, hnr⟩ := parent_of_owner c y ny hy h1 r hr hrs
    exact ⟨r, hpar, nr, hnr, hxo r hrx, hk.sym v nv r nr hv hnr hrv⟩
  have hnbS : ∀ y ny, g.node? y = some ny → x ∈ ny.owners → y.id.step ≤ g.current_step - 2 →
      ∀ v nv, g.node? v = some nv → x ∈ nv.owners → v ∈ ny.owners →
      ∃ r ∈ ny.sons, ∃ nr, g.node? r = some nr ∧ inS g x r = true ∧ v ∈ nr.owners := by
    intro y ny hy hxy h1 v nv hv hxv hvy
    have h0 : 0 ≤ y.id.step := by
      have := c.snn ny (List.mem_of_find?_eq_some hy); rw [node?_id_eq g y ny hy] at this; exact this
    obtain ⟨r, hr, hrv, hrx, hrs⟩ := ht y ny v nv nx hy hv hx hxy hxv hvy (y.id.step + 1) (by omega) (by omega)
    obtain ⟨hson, nr, hnr⟩ := son_of_owner c y ny hy h1 r hr hrs
    exact ⟨r, hson, nr, hnr, hxo r hrx, hk.sym v nv r nr hv hnr hrv⟩
  -- the pair rule of `g` against `x` gives an entry at every step, inside the set
  have hentry : ∀ y ny, g.node? y = some ny → x ∈ ny.owners → ∀ l, 0 ≤ l → l < g.current_step →
      ∃ r ∈ ny.owners, inS g x r = true ∧ r.id.step = l := by
    intro y ny hy hxy l h0 h1
    obtain ⟨r, hr, hrx, hrs⟩ := hk.pair y ny x nx hy hx hxy l h0 h1
    exact ⟨r, hr, hxo r hrx, hrs⟩
  -- `x` owns itself
  have hxx : x ∈ nx.owners := by
    have hxm := List.mem_of_find?_eq_some hx
    have hxid : nx.id = x := node?_id_eq g x nx hx
    have hok := ((isValidNode_iff g nx).mp (hk.valid x nx hx)).1
    have h0 : 0 ≤ x.id.step := by have := c.snn nx hxm; rw [hxid] at this; exact this
    have h1 : x.id.step < g.current_step := by have := c.below nx hxm; rw [hxid] at this; exact this
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok x.id.step
      (mem_intRange h0 (by omega)))
    have he := c.oos nx hxm q hq (by rw [eq_of_beq hqs, hxid])
    rw [hxid] at he
    rw [← he]; exact hq
  refine ⟨⟨?gow, ?gn, ?own, ?valid, ?sym, ?linkP, ?linkS, ?pair, ?nbrP, ?nbrS⟩, ?isv, ?below, ?pin⟩
  case gow =>
    intro p m hm
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hm
    exact List.mem_filter.mpr ⟨hk.gow p n hn, inS_of hn hxn⟩
  case gn =>
    intro q hq
    obtain ⟨nq, hnq, hxq⟩ := of_inS (List.mem_filter.mp hq).2
    rw [restrict_node? c.nd q nq hnq hxq]; rfl
  case own =>
    intro p m hm v hv
    obtain ⟨n, hn, _, rfl⟩ := restrict_node?_inv c.nd p m hm
    obtain ⟨hvn, hvs⟩ := List.mem_filter.mp hv
    exact List.mem_filter.mpr ⟨hk.own p n hn v hvn, hvs⟩
  case valid =>
    intro p m hm
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hm
    have hnm := List.mem_of_find?_eq_some hn
    have hnid : n.id = p := node?_id_eq g p n hn
    have hp0 : 0 ≤ p.id.step := by have := c.snn n hnm; rw [hnid] at this; exact this
    have hplt : p.id.step < g.current_step := by have := c.below n hnm; rw [hnid] at this; exact this
    obtain ⟨_, hroot, _⟩ := (isValidNode_iff g n).mp (hk.valid p n hn)
    refine (isValidNode_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · refine List.all_eq_true.mpr (fun l hl => ?_)
      obtain ⟨r, hr, hrs, hrl⟩ := hentry p n hn hxn l (mem_intRange_lower hl)
        (by have := mem_intRange_upper hl; rw [hcs] at this; omega)
      exact List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨hr, hrs⟩, beq_iff_eq.mpr hrl⟩
    · rcases hroot with hr | hr
      · exact Or.inl hr
      · refine Or.inr ?_
        obtain ⟨cc, hcc⟩ := List.exists_mem_of_ne_nil _ hr
        obtain ⟨ncc, hncc⟩ := hk.isNode_owner p n hn cc (hk.linkP p n hn cc hcc).1
        have hccs : cc.id.step = p.id.step - 1 := by
          have := c.pb n hnm cc hcc; rw [hnid] at this; exact this
        have hc0 : 0 ≤ cc.id.step := by
          have := c.snn ncc (List.mem_of_find?_eq_some hncc)
          rw [node?_id_eq g cc ncc hncc] at this; exact this
        have h1 : 1 ≤ p.id.step := by omega
        obtain ⟨r, hr', hrS, hrs⟩ := hentry p n hn hxn (p.id.step - 1) (by omega) (by omega)
        obtain ⟨hrp, _⟩ := parent_of_owner c p n hn h1 r hr' hrs
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hrp, hrS⟩)
    · by_cases hle : p.id.step ≤ g.current_step - 2
      · refine Or.inr ?_
        obtain ⟨r, hr', hrS, hrs⟩ := hentry p n hn hxn (p.id.step + 1) (by omega) (by omega)
        obtain ⟨hrs', _⟩ := son_of_owner c p n hn hle r hr' hrs
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hrs', hrS⟩)
      · refine Or.inl ?_
        show (n.id.id.step == g.current_step - 1) = true
        rw [hnid]
        exact beq_iff_eq.mpr (by omega)
  case sym =>
    intro p m q m' hp hq hqm
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hp
    obtain ⟨n', hn', _, rfl⟩ := restrict_node?_inv c.nd q m' hq
    obtain ⟨hqn, _⟩ := List.mem_filter.mp hqm
    exact List.mem_filter.mpr ⟨hk.sym p n q n' hn hn' hqn, inS_of hn hxn⟩
  case linkP =>
    intro p m hm cc hcc
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hm
    obtain ⟨hccn, hccS⟩ := List.mem_filter.mp hcc
    obtain ⟨hco, nc, hnc, hpc⟩ := hk.linkP p n hn cc hccn
    obtain ⟨nc', hnc', hxc⟩ := of_inS hccS
    rw [hnc] at hnc'; cases hnc'
    exact ⟨List.mem_filter.mpr ⟨hco, hccS⟩, rn g x nc, restrict_node? c.nd cc nc hnc hxc,
      List.mem_filter.mpr ⟨hpc, inS_of hn hxn⟩⟩
  case linkS =>
    intro p m hm cc hcc
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hm
    obtain ⟨hccn, hccS⟩ := List.mem_filter.mp hcc
    obtain ⟨hco, nc, hnc, hpc⟩ := hk.linkS p n hn cc hccn
    obtain ⟨nc', hnc', hxc⟩ := of_inS hccS
    rw [hnc] at hnc'; cases hnc'
    exact ⟨List.mem_filter.mpr ⟨hco, hccS⟩, rn g x nc, restrict_node? c.nd cc nc hnc hxc,
      List.mem_filter.mpr ⟨hpc, inS_of hn hxn⟩⟩
  case pair =>
    intro p m w mw hp hw hwm l h0 h1
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hp
    obtain ⟨n', hn', hxn', rfl⟩ := restrict_node?_inv c.nd w mw hw
    obtain ⟨hwn, _⟩ := List.mem_filter.mp hwm
    obtain ⟨r, hr, hrw, hrx, hrs⟩ := ht p n w n' nx hn hn' hx hxn hxn' hwn l h0 h1
    exact ⟨r, List.mem_filter.mpr ⟨hr, hxo r hrx⟩, List.mem_filter.mpr ⟨hrw, hxo r hrx⟩, hrs⟩
  case nbrP =>
    intro p m hm h1 v hv
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hm
    obtain ⟨hvn, hvS⟩ := List.mem_filter.mp hv
    obtain ⟨nv, hnv, hxv⟩ := of_inS hvS
    obtain ⟨r, hrp, nr, hnr, hrS, hvr⟩ := hnbP p n hn hxn h1 v nv hnv hxv hvn
    obtain ⟨nr', hnr', hxr⟩ := of_inS hrS
    rw [hnr] at hnr'; cases hnr'
    exact ⟨r, List.mem_filter.mpr ⟨hrp, hrS⟩, rn g x nr, restrict_node? c.nd r nr hnr hxr,
      List.mem_filter.mpr ⟨hvr, hvS⟩⟩
  case nbrS =>
    intro p m hm h1 v hv
    obtain ⟨n, hn, hxn, rfl⟩ := restrict_node?_inv c.nd p m hm
    obtain ⟨hvn, hvS⟩ := List.mem_filter.mp hv
    obtain ⟨nv, hnv, hxv⟩ := of_inS hvS
    obtain ⟨r, hrp, nr, hnr, hrS, hvr⟩ := hnbS p n hn hxn h1 v nv hnv hxv hvn
    obtain ⟨nr', hnr', hxr⟩ := of_inS hrS
    rw [hnr] at hnr'; cases hnr'
    exact ⟨r, List.mem_filter.mpr ⟨hrp, hrS⟩, rn g x nr, restrict_node? c.nd r nr hnr hxr,
      List.mem_filter.mpr ⟨hvr, hvS⟩⟩
  case isv =>
    unfold isValid
    refine List.all_eq_true.mpr (fun l hl => ?_)
    obtain ⟨r, hr, hrS, hrl⟩ := hentry x nx hx hxx l (mem_intRange_lower hl)
      (by have := mem_intRange_upper hl; rw [hcs] at this; omega)
    exact List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨hk.own x nx hx r hr, hrS⟩,
      beq_iff_eq.mpr hrl⟩
  case below =>
    refine ⟨rfl, fun q hq => (List.mem_filter.mp hq).1, fun p m hm => ?_⟩
    obtain ⟨n, hn, _, rfl⟩ := restrict_node?_inv c.nd p m hm
    exact ⟨n, hn, fun q hq => (List.mem_filter.mp hq).1, fun q hq => (List.mem_filter.mp hq).1,
      fun q hq => (List.mem_filter.mp hq).1⟩
  case pin =>
    intro z hz hzs
    obtain ⟨nz, hnz, hxz⟩ := of_inS (List.mem_filter.mp hz).2
    have hzid : nz.id = z := node?_id_eq g z nz hnz
    have he := c.oos nz (List.mem_of_find?_eq_some hnz) x hxz (by rw [hzid, hzs])
    rw [hzid] at he
    rw [he]

/-- **A pin survives when the pair rule holds with it as a fixed third member.** -/
theorem pin_survives_of_triPin {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (ht : TriPin g x) : isValid (filterAll g [x.id]) = true := by
  obtain ⟨hk, hv, hb, hpin⟩ := restrict_kernel c x nx hx ht
  exact isValid_filterAll_of_kernel hk hv hb [x.id]
    (fun r hr q hq hqs => by rw [List.mem_singleton.mp hr] at hqs ⊢; exact hpin q hq hqs)

-- ============================================================
-- The reader
-- ============================================================

section
variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)

theorem SAbove_reachable (g : GPathM) (h : Reachable reqOf forb g) : Sons.SAbove g := by
  induction h with
  | seed d title _ _ => exact Sons.SAbove_initSeed d title
  | up g d title hstep _ _ _ ih =>
    exact Sons.SAbove_up _ d title forb (by rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep)
      (Sons.SAbove_filterAll g (reqOf d) ih)
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact Sons.SAbove_join g₁ g₂ ih₁ ih₂
end

variable (φ : Cnf)

theorem pinCtx_readPins (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ps : List NodeId) (g : GPathM) (hp : ReadPins (filterAll kv.2 []) ps g) (hv : isValid g = true) :
    PinCtx g := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach
  obtain ⟨cm, _⟩ := SymMachine.machine_ctx φ hbd kv hkv
  have c₀ := Reader.RCtx_filterAll kv.2 cm []
  have cg := NoDeadEnd.rctx_readPins _ c₀ ps g hp
  have hsa : Sons.SAbove g := by
    have sa₀ := Sons.SAbove_filterAll kv.2 [] (SAbove_reachable (reqOf φ) (isProhibited φ) kv.2 hreach)
    clear hv cg
    induction hp with
    | start => exact sa₀
    | pin g _ q _ _ _ _ _ _ ih => exact Sons.SAbove_filterAll g [q.id] ih
  exact ⟨KernelReader.kernel_readPins φ hbd kv hkv ps g hp hv, cg.nodup, cg.oos, cg.shape.pbelow, hsa,
    cg.snn, cg.below⟩

/-- **`TriPin` at the first choice, along the reader.** -/
def TriPinReader (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, TriPin g q

/-- **`KernelSplit ⇐ TriPin` at the first choice.** -/
theorem kernelSplit_of_triPin (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ht : TriPinReader (filterAll kv.2 [])) : KernelReader.KernelSplit (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨q, hq, htq⟩ := ht g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := pinCtx_readPins φ hbd kv hkv ps g hp hv
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.ker.gn q (List.mem_filter.mp hq).1)
  obtain ⟨hk, hvh, hb, hpin⟩ := restrict_kernel c q nq hnq htq
  exact ⟨q, hq, restrictPin g q, hk, hvh, hb, hpin⟩

/-- **The reader decides `φ` when, at every valid state it visits, some node of the first choice
satisfies the pair rule with itself as a fixed third member.** -/
theorem readerVerdictW_iff_of_triPin (hbd : Bounded φ)
    (ht : ∀ kv ∈ pureRun φ, TriPinReader (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  KernelReader.readerVerdictW_iff_of_kernelSplit φ hbd
    (fun kv hkv => kernelSplit_of_triPin φ hbd kv hkv (ht kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.KernelSplit.restrict_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms restrict_kernel

/-- info: 'AbsSatBin.GraphPath.Model.KernelSplit.readerVerdictW_iff_of_triPin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_triPin

end AbsSatBin.GraphPath.Model.KernelSplit
