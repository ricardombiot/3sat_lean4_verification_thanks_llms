-- lean/improves_bin/AbsSatBin/GraphPath/Model/TriPinCut.lean
import AbsSatBin.GraphPath.Model.KernelSplit

/-!
# `KernelSplit ⇐ TriPin₁`: the sub-kernel after one round of cuts

`TriPin g x` asks every link `y–w` between two nodes that own `x` to have, at every step, a witness
that `x` also owns. It is measured false on a surviving pin (`ambhigh-dump`, `simple3sat_v3_c2`): the
link `y–w` is fine as a pair, but no solution goes through `x`, `y` and `w`, and the review cuts it.

So cut first. A link `y–w` is **`x`-compatible** (`Cx g x ny w`) when it has, at every step, a witness
that `x` also owns. The **cut sub-kernel** `restrictPin₁ g x` keeps the nodes that own `x` and, in
every table and every link list, only the `x`-compatible entries.

* **`TriPin₁ g x`**: the pair rule inside the cut sub-kernel. Two nodes that own `x` and have an
  `x`-compatible link share, at every step, a witness that `x` owns and that is an `x`-compatible entry
  of both. It is one round of cuts, no cascade.
* **`triPin₁_of_triPin`**: it is weaker than `TriPin`, which makes every link compatible.
* **`restrict₁_kernel`**: under `TriPin₁`, the cut sub-kernel is a valid kernel below `g` that fixes `x`.
  So **`KernelSplit ⇐ TriPin₁`** (`kernelSplit_of_triPin₁`, `readerVerdictW_iff_of_triPin₁`).

Why the clauses hold: `x`-compatibility is symmetric (`cx_symm`); every node that owns `x` has an
`x`-compatible link to itself and to `x` (`cx_self`, `cx_x`), so `TriPin₁` at `(y, y)` gives entries at
every step; the neighbour clause is `TriPin₁` at the adjacent step, as for `TriPin`.
-/

namespace AbsSatBin.GraphPath.Model.TriPinCut

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

-- ============================================================
-- `x`-compatible links
-- ============================================================

/-- The link from `ny` to `w` has, at every step, a witness that `x` also owns. -/
def Cx (g : GPathM) (x : PathNodeId) (ny : PNodeM) (w : PathNodeId) : Prop :=
  ∃ nw nx, g.node? w = some nw ∧ g.node? x = some nx ∧ w ∈ ny.owners ∧
    ∀ l, 0 ≤ l → l < g.current_step → ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l

def shareAt (ny nw nx : PNodeM) (l : Int) : Bool :=
  ny.owners.any (fun r => r.id.step == l && nw.owners.contains r && nx.owners.contains r)

/-- `Cx`, as a test. -/
def cx (g : GPathM) (x : PathNodeId) (ny : PNodeM) (w : PathNodeId) : Bool :=
  match g.node? w, g.node? x with
  | some nw, some nx => ny.owners.contains w && (intRange 0 (g.current_step - 1)).all (shareAt ny nw nx)
  | _, _ => false

theorem shareAt_of {ny nw nx : PNodeM} {l : Int} (h : shareAt ny nw nx l = true) :
    ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l := by
  obtain ⟨r, hr, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨hs, hw⟩, hx⟩ := hb
  exact ⟨r, hr, List.mem_of_elem_eq_true hw, List.mem_of_elem_eq_true hx, eq_of_beq hs⟩

theorem shareAt_mk {ny nw nx : PNodeM} {l : Int} (r : PathNodeId) (hr : r ∈ ny.owners)
    (hw : r ∈ nw.owners) (hx : r ∈ nx.owners) (hs : r.id.step = l) : shareAt ny nw nx l = true := by
  refine List.any_eq_true.mpr ⟨r, hr, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨beq_iff_eq.mpr hs, List.elem_eq_true_of_mem hw⟩, List.elem_eq_true_of_mem hx⟩

theorem cx_of {g : GPathM} {x : PathNodeId} {ny : PNodeM} {w : PathNodeId} (h : Cx g x ny w) :
    cx g x ny w = true := by
  obtain ⟨nw, nx, hnw, hnx, hwy, hl⟩ := h
  unfold cx; rw [hnw, hnx]
  simp only [Bool.and_eq_true]
  refine ⟨List.elem_eq_true_of_mem hwy, List.all_eq_true.mpr (fun l hl' => ?_)⟩
  obtain ⟨r, hr, hrw, hrx, hrs⟩ := hl l (mem_intRange_lower hl')
    (by have := mem_intRange_upper hl'; omega)
  exact shareAt_mk r hr hrw hrx hrs

theorem of_cx {g : GPathM} {x : PathNodeId} {ny : PNodeM} {w : PathNodeId} (h : cx g x ny w = true) :
    Cx g x ny w := by
  unfold cx at h
  cases hnw : g.node? w with
  | none => rw [hnw] at h; cases h
  | some nw =>
    cases hnx : g.node? x with
    | none => rw [hnw, hnx] at h; cases h
    | some nx =>
      rw [hnw, hnx] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hwy, hall⟩ := h
      refine ⟨nw, nx, hnw, hnx, List.mem_of_elem_eq_true hwy, fun l h0 h1 => ?_⟩
      exact shareAt_of (List.all_eq_true.mp hall l (mem_intRange h0 (by omega)))

/-- What the cut sub-kernel keeps from a list of `ny`: nodes that own `x`, `x`-compatible with `ny`. -/
def keep (g : GPathM) (x : PathNodeId) (ny : PNodeM) (v : PathNodeId) : Bool :=
  inS g x v && cx g x ny v

theorem mem_keep_of {g : GPathM} {x : PathNodeId} {ny : PNodeM} {l : List PathNodeId} {v : PathNodeId}
    (h : v ∈ l.filter (keep g x ny)) : v ∈ l ∧ inS g x v = true ∧ Cx g x ny v := by
  obtain ⟨hv, hk⟩ := List.mem_filter.mp h
  unfold keep at hk
  simp only [Bool.and_eq_true] at hk
  exact ⟨hv, hk.1, of_cx hk.2⟩

theorem mem_keep {g : GPathM} {x : PathNodeId} {ny : PNodeM} {l : List PathNodeId} {v : PathNodeId}
    (hv : v ∈ l) (hs : inS g x v = true) (hc : Cx g x ny v) : v ∈ l.filter (keep g x ny) := by
  refine List.mem_filter.mpr ⟨hv, ?_⟩
  unfold keep
  simp only [Bool.and_eq_true]
  exact ⟨hs, cx_of hc⟩

-- ============================================================
-- The cut sub-kernel
-- ============================================================

/-- A node cut down to the cut sub-kernel. -/
def rn₁ (g : GPathM) (x : PathNodeId) (n : PNodeM) : PNodeM :=
  { n with owners := n.owners.filter (keep g x n), parents := n.parents.filter (keep g x n),
           sons := n.sons.filter (keep g x n) }

/-- **The cut sub-kernel of `x`**: the nodes that own `x`, with only `x`-compatible entries and links. -/
def restrictPin₁ (g : GPathM) (x : PathNodeId) : GPathM :=
  { nodes := (g.nodes.filter (fun n => n.owners.contains x)).map (rn₁ g x),
    gowners := g.gowners.filter (inS g x),
    current_step := g.current_step,
    map_parent := g.map_parent }

section
variable {g : GPathM} {x : PathNodeId}

theorem nodup_restrict₁ (hnd : NodupIds g) : NodupIds (restrictPin₁ g x) := by
  unfold NodupIds at hnd ⊢
  show (((g.nodes.filter (fun n => n.owners.contains x)).map (rn₁ g x)).map (·.id)).Nodup
  rw [List.map_map]
  have he : ((·.id) ∘ rn₁ g x) = (fun n : PNodeM => n.id) := rfl
  rw [he]
  exact List.Sublist.nodup (List.Sublist.map _ List.filter_sublist) hnd

theorem restrict₁_node?_inv (hnd : NodupIds g) (p : PathNodeId) (m : PNodeM)
    (h : (restrictPin₁ g x).node? p = some m) :
    ∃ n, g.node? p = some n ∧ x ∈ n.owners ∧ m = rn₁ g x n := by
  have hm := List.mem_of_find?_eq_some h
  have hid := node?_id_eq _ p m h
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hng, hc⟩ := List.mem_filter.mp hn
  have hnid : n.id = p := hid
  exact ⟨n, by rw [← hnid]; exact node?_of_mem hnd n hng, List.mem_of_elem_eq_true hc, rfl⟩

theorem restrict₁_node? (hnd : NodupIds g) (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n)
    (hx : x ∈ n.owners) : (restrictPin₁ g x).node? p = some (rn₁ g x n) := by
  have hmem : rn₁ g x n ∈ (restrictPin₁ g x).nodes :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hn,
      List.elem_eq_true_of_mem hx⟩)
  have := node?_of_mem (nodup_restrict₁ (x := x) hnd) _ hmem
  have hid : (rn₁ g x n).id = p := node?_id_eq g p n hn
  rw [hid] at this
  exact this
end

-- ============================================================
-- `TriPin₁`
-- ============================================================

/-- **`TriPin₁`**: the pair rule inside the cut sub-kernel. -/
def TriPin₁ (g : GPathM) (x : PathNodeId) : Prop :=
  ∀ y ny w nw nx, g.node? y = some ny → g.node? w = some nw → g.node? x = some nx →
    x ∈ ny.owners → x ∈ nw.owners → Cx g x ny w →
    ∀ l, 0 ≤ l → l < g.current_step → ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧
      r.id.step = l ∧ Cx g x ny r ∧ Cx g x nw r

section
variable {g : GPathM} (c : PinCtx g)
include c

theorem self_own_pc (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny) : y ∈ ny.owners := by
  have hym := List.mem_of_find?_eq_some hy
  have hyid : ny.id = y := node?_id_eq g y ny hy
  have hok := ((isValidNode_iff g ny).mp (c.ker.valid y ny hy)).1
  have h0 : 0 ≤ y.id.step := by have := c.snn ny hym; rw [hyid] at this; exact this
  have h1 : y.id.step < g.current_step := by have := c.below ny hym; rw [hyid] at this; exact this
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok y.id.step
    (mem_intRange h0 (by omega)))
  have he := c.oos ny hym q hq (by rw [eq_of_beq hqs, hyid])
  rw [hyid] at he
  rw [← he]; exact hq

/-- `x`-compatibility is symmetric. -/
theorem cx_symm {x y w : PathNodeId} {ny nw : PNodeM} (hy : g.node? y = some ny)
    (hw : g.node? w = some nw) (h : Cx g x ny w) : Cx g x nw y := by
  obtain ⟨nw', nx, hw', hx, hwy, hl⟩ := h
  rw [hw] at hw'; cases hw'
  refine ⟨ny, nx, hy, hx, c.ker.sym y ny w nw hy hw hwy, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrw, hrx, hrs⟩ := hl l h0 h1
  exact ⟨r, hrw, hr, hrx, hrs⟩

/-- A node that owns `x` has an `x`-compatible link to itself. -/
theorem cx_self {x y : PathNodeId} {nx ny : PNodeM} (hx : g.node? x = some nx) (hy : g.node? y = some ny)
    (hxy : x ∈ ny.owners) : Cx g x ny y := by
  refine ⟨ny, nx, hy, hx, self_own_pc c y ny hy, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrx, hrs⟩ := c.ker.pair y ny x nx hy hx hxy l h0 h1
  exact ⟨r, hr, hr, hrx, hrs⟩

/-- **`TriPin ⇒ TriPin₁`**: every link is `x`-compatible under `TriPin`. -/
theorem triPin₁_of_triPin (x : PathNodeId) (ht : TriPin g x) : TriPin₁ g x := by
  intro y ny w nw nx hy hw hx hxy hxw hC l h0 h1
  obtain ⟨_, _, _, _, hwy, _⟩ := hC
  obtain ⟨r, hry, hrw, hrx, hrs⟩ := ht y ny w nw nx hy hw hx hxy hxw hwy l h0 h1
  obtain ⟨nr, hnr⟩ := c.ker.isNode_owner y ny hy r hry
  have hxr : x ∈ nr.owners := c.ker.sym x nx r nr hx hnr hrx
  refine ⟨r, hry, hrw, hrx, hrs, ⟨nr, nx, hnr, hx, hry, ?_⟩, ⟨nr, nx, hnr, hx, hrw, ?_⟩⟩
  · exact fun l' h0' h1' => ht y ny r nr nx hy hnr hx hxy hxr hry l' h0' h1'
  · exact fun l' h0' h1' => ht w nw r nr nx hw hnr hx hxw hxr hrw l' h0' h1'
end

-- ============================================================
-- The cut sub-kernel is a valid kernel below the state
-- ============================================================

theorem restrict₁_kernel {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (ht : TriPin₁ g x) :
    Kernel (restrictPin₁ g x) ∧ isValid (restrictPin₁ g x) = true ∧ Below g (restrictPin₁ g x) ∧
      ∀ z ∈ (restrictPin₁ g x).gowners, z.id.step = x.id.step → z.id = x.id := by
  have hk := c.ker
  have hxo : ∀ r ∈ nx.owners, inS g x r = true := by
    intro r hr
    obtain ⟨nr, hnr⟩ := hk.isNode_owner x nx hx r hr
    exact inS_of hnr (hk.sym x nx r nr hx hnr hr)
  have hcs : (restrictPin₁ g x).current_step = g.current_step := rfl
  -- entries at every step, compatible: `TriPin₁` at `(y, y)`
  have hentry : ∀ y ny, g.node? y = some ny → x ∈ ny.owners → ∀ l, 0 ≤ l → l < g.current_step →
      ∃ r ∈ ny.owners, inS g x r = true ∧ Cx g x ny r ∧ r.id.step = l := by
    intro y ny hy hxy l h0 h1
    obtain ⟨r, hr, _, hrx, hrs, hcr, _⟩ := ht y ny y ny nx hy hy hx hxy hxy (cx_self c hx hy hxy) l h0 h1
    exact ⟨r, hr, hxo r hrx, hcr, hrs⟩
  -- the neighbour clause, from `TriPin₁` at the adjacent step
  have hnbP : ∀ y ny, g.node? y = some ny → x ∈ ny.owners → 1 ≤ y.id.step →
      ∀ v nv, g.node? v = some nv → x ∈ nv.owners → Cx g x ny v →
      ∃ r ∈ ny.parents, ∃ nr, g.node? r = some nr ∧ inS g x r = true ∧ Cx g x ny r ∧
        v ∈ nr.owners ∧ Cx g x nr v := by
    intro y ny hy hxy h1 v nv hv hxv hcv
    -- idx: adjacent gpath rows (one row per map step, bin map too)
    have hlt : y.id.step - 1 < g.current_step := by
      have := c.below ny (List.mem_of_find?_eq_some hy); rw [node?_id_eq g y ny hy] at this; omega
    -- idx: adjacent gpath rows (one row per map step, bin map too)
    obtain ⟨r, hr, hrv, hrx, hrs, hcyr, hcvr⟩ := ht y ny v nv nx hy hv hx hxy hxv hcv (y.id.step - 1)
      (by omega) hlt
    obtain ⟨hpar, nr, hnr⟩ := parent_of_owner c y ny hy h1 r hr hrs
    exact ⟨r, hpar, nr, hnr, hxo r hrx, hcyr, hk.sym v nv r nr hv hnr hrv, cx_symm c hv hnr hcvr⟩
  have hnbS : ∀ y ny, g.node? y = some ny → x ∈ ny.owners → y.id.step ≤ g.current_step - 2 →
      ∀ v nv, g.node? v = some nv → x ∈ nv.owners → Cx g x ny v →
      ∃ r ∈ ny.sons, ∃ nr, g.node? r = some nr ∧ inS g x r = true ∧ Cx g x ny r ∧
        v ∈ nr.owners ∧ Cx g x nr v := by
    intro y ny hy hxy h1 v nv hv hxv hcv
    have h0 : 0 ≤ y.id.step := by
      have := c.snn ny (List.mem_of_find?_eq_some hy); rw [node?_id_eq g y ny hy] at this; exact this
    -- idx: adjacent gpath rows (one row per map step, bin map too)
    obtain ⟨r, hr, hrv, hrx, hrs, hcyr, hcvr⟩ := ht y ny v nv nx hy hv hx hxy hxv hcv (y.id.step + 1)
      (by omega) (by omega)
    obtain ⟨hson, nr, hnr⟩ := son_of_owner c y ny hy h1 r hr hrs
    exact ⟨r, hson, nr, hnr, hxo r hrx, hcyr, hk.sym v nv r nr hv hnr hrv, cx_symm c hv hnr hcvr⟩
  have hxx : x ∈ nx.owners := self_own_pc c x nx hx
  refine ⟨⟨?gow, ?gn, ?own, ?valid, ?sym, ?linkP, ?linkS, ?pair, ?nbrP, ?nbrS⟩, ?isv, ?below, ?pin⟩
  case gow =>
    intro p m hm
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    exact List.mem_filter.mpr ⟨hk.gow p n hn, inS_of hn hxn⟩
  case gn =>
    intro q hq
    obtain ⟨nq, hnq, hxq⟩ := of_inS (List.mem_filter.mp hq).2
    rw [restrict₁_node? c.nd q nq hnq hxq]; rfl
  case own =>
    intro p m hm v hv
    obtain ⟨n, hn, _, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    obtain ⟨hvn, hvs, _⟩ := mem_keep_of hv
    exact List.mem_filter.mpr ⟨hk.own p n hn v hvn, hvs⟩
  case valid =>
    intro p m hm
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    have hnm := List.mem_of_find?_eq_some hn
    have hnid : n.id = p := node?_id_eq g p n hn
    have hp0 : 0 ≤ p.id.step := by have := c.snn n hnm; rw [hnid] at this; exact this
    have hplt : p.id.step < g.current_step := by have := c.below n hnm; rw [hnid] at this; exact this
    obtain ⟨_, hroot, _⟩ := (isValidNode_iff g n).mp (hk.valid p n hn)
    refine (isValidNode_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · refine List.all_eq_true.mpr (fun l hl => ?_)
      obtain ⟨r, hr, hrs, hcr, hrl⟩ := hentry p n hn hxn l (mem_intRange_lower hl)
        (by have := mem_intRange_upper hl; rw [hcs] at this; omega)
      exact List.any_eq_true.mpr ⟨r, mem_keep hr hrs hcr, beq_iff_eq.mpr hrl⟩
    · rcases hroot with hr | hr
      · exact Or.inl hr
      · refine Or.inr ?_
        obtain ⟨cc, hcc⟩ := List.exists_mem_of_ne_nil _ hr
        obtain ⟨ncc, hncc⟩ := hk.isNode_owner p n hn cc (hk.linkP p n hn cc hcc).1
        -- idx: adjacent gpath rows (one row per map step, bin map too)
        have hccs : cc.id.step = p.id.step - 1 := by
          have := c.pb n hnm cc hcc; rw [hnid] at this; exact this
        have hc0 : 0 ≤ cc.id.step := by
          have := c.snn ncc (List.mem_of_find?_eq_some hncc)
          rw [node?_id_eq g cc ncc hncc] at this; exact this
        have h1 : 1 ≤ p.id.step := by omega
        -- idx: adjacent gpath rows (one row per map step, bin map too)
        obtain ⟨r, hr', hrS, hcr, hrs⟩ := hentry p n hn hxn (p.id.step - 1) (by omega) (by omega)
        obtain ⟨hrp, _⟩ := parent_of_owner c p n hn h1 r hr' hrs
        exact List.ne_nil_of_mem (mem_keep hrp hrS hcr)
    · by_cases hle : p.id.step ≤ g.current_step - 2
      · refine Or.inr ?_
        -- idx: adjacent gpath rows (one row per map step, bin map too)
        obtain ⟨r, hr', hrS, hcr, hrs⟩ := hentry p n hn hxn (p.id.step + 1) (by omega) (by omega)
        obtain ⟨hrs', _⟩ := son_of_owner c p n hn hle r hr' hrs
        exact List.ne_nil_of_mem (mem_keep hrs' hrS hcr)
      · refine Or.inl ?_
        show (n.id.id.step == g.current_step - 1) = true
        rw [hnid]
        exact beq_iff_eq.mpr (by omega)
  case sym =>
    intro p m q m' hp hq hqm
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hp
    obtain ⟨n', hn', _, rfl⟩ := restrict₁_node?_inv c.nd q m' hq
    obtain ⟨hqn, _, hcq⟩ := mem_keep_of hqm
    exact mem_keep (hk.sym p n q n' hn hn' hqn) (inS_of hn hxn) (cx_symm c hn hn' hcq)
  case linkP =>
    intro p m hm cc hcc
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    obtain ⟨hccn, hccS, hccC⟩ := mem_keep_of hcc
    obtain ⟨hco, nc, hnc, hpc⟩ := hk.linkP p n hn cc hccn
    obtain ⟨nc', hnc', hxc⟩ := of_inS hccS
    rw [hnc] at hnc'; cases hnc'
    exact ⟨mem_keep hco hccS hccC, rn₁ g x nc, restrict₁_node? c.nd cc nc hnc hxc,
      mem_keep hpc (inS_of hn hxn) (cx_symm c hn hnc hccC)⟩
  case linkS =>
    intro p m hm cc hcc
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    obtain ⟨hccn, hccS, hccC⟩ := mem_keep_of hcc
    obtain ⟨hco, nc, hnc, hpc⟩ := hk.linkS p n hn cc hccn
    obtain ⟨nc', hnc', hxc⟩ := of_inS hccS
    rw [hnc] at hnc'; cases hnc'
    exact ⟨mem_keep hco hccS hccC, rn₁ g x nc, restrict₁_node? c.nd cc nc hnc hxc,
      mem_keep hpc (inS_of hn hxn) (cx_symm c hn hnc hccC)⟩
  case pair =>
    intro p m w mw hp hw hwm l h0 h1
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hp
    obtain ⟨n', hn', hxn', rfl⟩ := restrict₁_node?_inv c.nd w mw hw
    obtain ⟨_, _, hcw⟩ := mem_keep_of hwm
    obtain ⟨r, hr, hrw, hrx, hrs, hcr, hcr'⟩ := ht p n w n' nx hn hn' hx hxn hxn' hcw l h0 h1
    exact ⟨r, mem_keep hr (hxo r hrx) hcr, mem_keep hrw (hxo r hrx) hcr', hrs⟩
  case nbrP =>
    intro p m hm h1 v hv
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    obtain ⟨_, hvS, hcv⟩ := mem_keep_of hv
    obtain ⟨nv, hnv, hxv⟩ := of_inS hvS
    obtain ⟨r, hrp, nr, hnr, hrS, hcr, hvr, hcrv⟩ := hnbP p n hn hxn h1 v nv hnv hxv hcv
    obtain ⟨nr', hnr', hxr⟩ := of_inS hrS
    rw [hnr] at hnr'; cases hnr'
    exact ⟨r, mem_keep hrp hrS hcr, rn₁ g x nr, restrict₁_node? c.nd r nr hnr hxr, mem_keep hvr hvS hcrv⟩
  case nbrS =>
    intro p m hm h1 v hv
    obtain ⟨n, hn, hxn, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    obtain ⟨_, hvS, hcv⟩ := mem_keep_of hv
    obtain ⟨nv, hnv, hxv⟩ := of_inS hvS
    obtain ⟨r, hrp, nr, hnr, hrS, hcr, hvr, hcrv⟩ := hnbS p n hn hxn h1 v nv hnv hxv hcv
    obtain ⟨nr', hnr', hxr⟩ := of_inS hrS
    rw [hnr] at hnr'; cases hnr'
    exact ⟨r, mem_keep hrp hrS hcr, rn₁ g x nr, restrict₁_node? c.nd r nr hnr hxr, mem_keep hvr hvS hcrv⟩
  case isv =>
    unfold isValid
    refine List.all_eq_true.mpr (fun l hl => ?_)
    obtain ⟨r, hr, hrS, _, hrl⟩ := hentry x nx hx hxx l (mem_intRange_lower hl)
      (by have := mem_intRange_upper hl; rw [hcs] at this; omega)
    exact List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨hk.own x nx hx r hr, hrS⟩,
      beq_iff_eq.mpr hrl⟩
  case below =>
    refine ⟨rfl, fun q hq => (List.mem_filter.mp hq).1, fun p m hm => ?_⟩
    obtain ⟨n, hn, _, rfl⟩ := restrict₁_node?_inv c.nd p m hm
    exact ⟨n, hn, fun q hq => (List.mem_filter.mp hq).1, fun q hq => (List.mem_filter.mp hq).1,
      fun q hq => (List.mem_filter.mp hq).1⟩
  case pin =>
    intro z hz hzs
    obtain ⟨nz, hnz, hxz⟩ := of_inS (List.mem_filter.mp hz).2
    have hzid : nz.id = z := node?_id_eq g z nz hnz
    have he := c.oos nz (List.mem_of_find?_eq_some hnz) x hxz (by rw [hzid, hzs])
    rw [hzid] at he
    rw [he]

/-- **A pin survives when the pair rule holds inside its cut sub-kernel.** -/
theorem pin_survives_of_triPin₁ {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (ht : TriPin₁ g x) : isValid (filterAll g [x.id]) = true := by
  obtain ⟨hk, hv, hb, hpin⟩ := restrict₁_kernel c x nx hx ht
  exact isValid_filterAll_of_kernel hk hv hb [x.id]
    (fun r hr q hq hqs => by rw [List.mem_singleton.mp hr] at hqs ⊢; exact hpin q hq hqs)

-- ============================================================
-- The reader
-- ============================================================

variable (φ : Cnf)

/-- **`TriPin₁` at the first choice, along the reader.** -/
def TriPin₁Reader (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, TriPin₁ g q

/-- **`KernelSplit ⇐ TriPin₁` at the first choice.** -/
theorem kernelSplit_of_triPin₁ (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ht : TriPin₁Reader (filterAll kv.2 [])) : KernelReader.KernelSplit (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨q, hq, htq⟩ := ht g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := pinCtx_readPins φ hbd kv hkv ps g hp hv
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.ker.gn q (List.mem_filter.mp hq).1)
  obtain ⟨hk, hvh, hb, hpin⟩ := restrict₁_kernel c q nq hnq htq
  exact ⟨q, hq, restrictPin₁ g q, hk, hvh, hb, hpin⟩

/-- **The reader decides `φ` when, at every valid state it visits, some node of the first choice
satisfies the pair rule inside its cut sub-kernel.** -/
theorem readerVerdictW_iff_of_triPin₁ (hbd : Bounded φ)
    (ht : ∀ kv ∈ pureRun φ, TriPin₁Reader (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  KernelReader.readerVerdictW_iff_of_kernelSplit φ hbd
    (fun kv hkv => kernelSplit_of_triPin₁ φ hbd kv hkv (ht kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.TriPinCut.restrict₁_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms restrict₁_kernel

/-- info: 'AbsSatBin.GraphPath.Model.TriPinCut.triPin₁_of_triPin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triPin₁_of_triPin

/-- info: 'AbsSatBin.GraphPath.Model.TriPinCut.readerVerdictW_iff_of_triPin₁' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_triPin₁

end AbsSatBin.GraphPath.Model.TriPinCut
