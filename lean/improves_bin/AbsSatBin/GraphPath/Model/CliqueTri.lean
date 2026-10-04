-- lean/improves_bin/AbsSatBin/GraphPath/Model/CliqueTri.lean
import AbsSatBin.GraphPath.Model.TriPinAll
import AbsSatBin.GraphPath.Model.AmbTriCore

/-!
# `CliqueTri`: `TriPin₁` relative to every clique, and why the pin keeps it

`AllTriPin₁` cannot be an invariant on its own: after a pin at `x`, `x` is in every table, so `TriPin₁`
for the next node `x'` is a statement about `x` and `x'` together in the previous state. The closed
form is relative to any set of nodes that own each other.

* **`TriP g P`**: restrict to the nodes that own every member of `P`; a link `y–w` is `P`-compatible
  (`CxP`) when it has, at every step, a witness that owns `P`; the pair rule holds on the `P`-compatible
  links, with `P`-compatible witnesses. `TriP g []` is the kernel's pair rule (`triP_nil`), and
  `TriP g [x]` is `TriPin₁ g x` (`triPin₁_of_triP`).
* **`CliqueTri g`**: `TriP g P` for every clique `P`. It gives `AllTriPin₁` (`allTriPin₁_of_cliqueTri`).

**The pin keeps it** (`cliqueTri_pin`). Let `x` be a node of the reader's first choice, with
`TriPin₁ g x`, and `g' = filterAll g [x.id]`:
1. **The pin is the cut sub-kernel** (`pin_eq_cut`): the tables of `g'` are exactly those of
   `restrictPin₁ g x`. One inclusion is `below_filterAll` (the review never goes below a kernel). For
   the other, every node of `g'` owns `x` (the prefix is fixed, so `x` is the only entry of its step)
   and every link of `g'` has its witnesses in `g'`, which all own `x`.
2. **A clique of `g'` is a clique of `g` with `x` added** (`cliqueTri_of_cut`), and `TriP g (x :: P)`,
   applied twice, gives `TriP g' P`: once for the witness, once more for the witnesses of the
   witness's links (the nested compatibility the cut asks for).

So along the reader **`CliqueTri` only has to hold at the starting states** (`cliqueTri_reader`,
`readerVerdictW_iff_of_cliqueTri`): what is left is a statement about the machine's output alone.
-/

namespace AbsSatBin.GraphPath.Model.CliqueTri

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCut
open AbsSatBin.GraphPath.Model.TriPinAll
open AbsSatBin.GraphPath.Model.AmbTriCore
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

-- ============================================================
-- Definitions
-- ============================================================

/-- The table holds every member of `P`. -/
def OwnsAll (P : List PathNodeId) (n : PNodeM) : Prop := ∀ p ∈ P, p ∈ n.owners

/-- The link from `ny` to `w` has, at every step, a witness that owns `P`. -/
def CxP (g : GPathM) (P : List PathNodeId) (ny : PNodeM) (w : PathNodeId) : Prop :=
  ∃ nw, g.node? w = some nw ∧ w ∈ ny.owners ∧ ∀ l, 0 ≤ l → l < g.current_step →
    ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r.id.step = l ∧ ∃ nr, g.node? r = some nr ∧ OwnsAll P nr

/-- **The pair rule relative to `P`**, on `P`-compatible links, with `P`-compatible witnesses. -/
def TriP (g : GPathM) (P : List PathNodeId) : Prop :=
  ∀ y ny w nw, g.node? y = some ny → g.node? w = some nw → OwnsAll P ny → OwnsAll P nw →
    CxP g P ny w → ∀ l, 0 ≤ l → l < g.current_step →
      ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r.id.step = l ∧ (∃ nr, g.node? r = some nr ∧ OwnsAll P nr) ∧
        CxP g P ny r ∧ CxP g P nw r

/-- Live nodes that own each other (and themselves). -/
def Clique (g : GPathM) (P : List PathNodeId) : Prop := ∀ p ∈ P, ∃ np, g.node? p = some np ∧ OwnsAll P np

/-- **`CliqueTri`**: the pair rule relative to every clique. -/
def CliqueTri (g : GPathM) : Prop := ∀ P, Clique g P → TriP g P

-- ============================================================
-- The two ends: `[]` is the kernel, `[x]` is `TriPin₁`
-- ============================================================

section
variable {g : GPathM} (c : PinCtx g)
include c

theorem cxP_nil (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny) (r : PathNodeId)
    (hr : r ∈ ny.owners) : CxP g [] ny r := by
  obtain ⟨nr, hnr⟩ := c.ker.isNode_owner y ny hy r hr
  refine ⟨nr, hnr, hr, fun l h0 h1 => ?_⟩
  obtain ⟨s, hs, hsr, hss⟩ := c.ker.pair y ny r nr hy hnr hr l h0 h1
  obtain ⟨ns, hns⟩ := c.ker.isNode_owner y ny hy s hs
  exact ⟨s, hs, hsr, hss, ns, hns, fun _ h => absurd h List.not_mem_nil⟩

/-- `TriP g []` is the kernel's pair rule. -/
theorem triP_nil : TriP g [] := by
  intro y ny w nw hy hw _ _ hC l h0 h1
  obtain ⟨_, _, hwy, _⟩ := hC
  obtain ⟨r, hr, hrw, hrs⟩ := c.ker.pair y ny w nw hy hw hwy l h0 h1
  obtain ⟨nr, hnr⟩ := c.ker.isNode_owner y ny hy r hr
  exact ⟨r, hr, hrw, hrs, ⟨nr, hnr, fun _ h => absurd h List.not_mem_nil⟩, cxP_nil c y ny hy r hr,
    cxP_nil c w nw hw r hrw⟩

/-- A `P`-compatible link with `x ∈ P` is `x`-compatible. -/
theorem cx_of_cxP {x : PathNodeId} {nx : PNodeM} (hx : g.node? x = some nx) {P : List PathNodeId}
    (hxP : x ∈ P) {nz : PNodeM} {v : PathNodeId} (h : CxP g P nz v) : Cx g x nz v := by
  obtain ⟨nv, hnv, hvz, hl⟩ := h
  refine ⟨nv, nx, hnv, hx, hvz, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrv, hrs, nr, hnr, hown⟩ := hl l h0 h1
  exact ⟨r, hr, hrv, c.ker.sym r nr x nx hnr hx (hown x hxP), hrs⟩

/-- A `P`-compatible link from `nz` to `v`, with `v` owning `P`, makes every member of `P`
`x`-compatible with `v`. -/
theorem cx_member {x : PathNodeId} {nx : PNodeM} (hx : g.node? x = some nx) {P : List PathNodeId}
    (hxP : x ∈ P) {nz nv : PNodeM} {v : PathNodeId} (hnv : g.node? v = some nv) (hvP : OwnsAll P nv)
    (h : CxP g P nz v) (p : PathNodeId) (np : PNodeM) (hnp : g.node? p = some np) (hpP : p ∈ P) :
    Cx g x nv p := by
  obtain ⟨nv', hnv', _, hl⟩ := h
  rw [hnv] at hnv'; cases hnv'
  refine ⟨np, nx, hnp, hx, hvP p hpP, fun l h0 h1 => ?_⟩
  obtain ⟨r, _, hrv, hrs, nr, hnr, hown⟩ := hl l h0 h1
  exact ⟨r, hrv, c.ker.sym r nr p np hnr hnp (hown p hpP), c.ker.sym r nr x nx hnr hx (hown x hxP), hrs⟩

/-- **`TriP g [x]` gives `TriPin₁ g x`.** -/
theorem triPin₁_of_triP (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) (h : TriP g [x]) :
    TriPin₁ g x := by
  have hxP : x ∈ [x] := List.mem_singleton.mpr rfl
  have own1 : ∀ n : PNodeM, x ∈ n.owners → OwnsAll [x] n := fun n hn p hp => by
    rw [List.mem_singleton.mp hp]; exact hn
  intro y ny w nw nx' hy hw hx' hxy hxw hC l h0 h1
  rw [hx] at hx'; cases hx'
  obtain ⟨nw', nx'', hw', hx'', hwy, hl⟩ := hC
  rw [hw] at hw'; cases hw'
  rw [hx] at hx''; cases hx''
  have hC' : CxP g [x] ny w := ⟨nw, hw, hwy, fun l' h0' h1' => by
    obtain ⟨r, hr, hrw, hrx, hrs⟩ := hl l' h0' h1'
    obtain ⟨nr, hnr⟩ := c.ker.isNode_owner y ny hy r hr
    exact ⟨r, hr, hrw, hrs, nr, hnr, own1 nr (c.ker.sym x nx r nr hx hnr hrx)⟩⟩
  obtain ⟨r, hr, hrw, hrs, ⟨nr, hnr, hrown⟩, cy, cw⟩ :=
    h y ny w nw hy hw (own1 ny hxy) (own1 nw hxw) hC' l h0 h1
  exact ⟨r, hr, hrw, c.ker.sym r nr x nx hnr hx (hrown x hxP), hrs, cx_of_cxP c hx hxP cy,
    cx_of_cxP c hx hxP cw⟩

/-- **`CliqueTri ⇒ AllTriPin₁`.** -/
theorem allTriPin₁_of_cliqueTri (h : CliqueTri g) : AllTriPin₁ g := by
  intro x nx hx
  refine triPin₁_of_triP c x nx hx (h [x] (fun p hp => ?_))
  rw [List.mem_singleton.mp hp]
  exact ⟨nx, hx, fun q hq => by rw [List.mem_singleton.mp hq]; exact self_own_pc c x nx hx⟩
end

-- ============================================================
-- A state whose tables are the cut tables of `g` keeps `CliqueTri`
-- ============================================================

/-- **The pair rule relative to a clique `P` passes to a state with the cut tables of `x`**, from the
pair rule relative to `x :: P` (which is a clique of `g`). -/
theorem triP_of_cut {g g' : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx)
    (hE0 : ∀ p nh, g'.node? p = some nh → ∃ n, g.node? p = some n)
    (hE1 : ∀ p nh n, g'.node? p = some nh → g.node? p = some n →
      x ∈ n.owners ∧ ∀ q, q ∈ nh.owners ↔ (q ∈ n.owners ∧ inS g x q = true ∧ Cx g x n q))
    (hE2 : ∀ p n, g.node? p = some n → x ∈ n.owners → ∃ nh, g'.node? p = some nh)
    (hcs : g'.current_step = g.current_step) (P : List PathNodeId) (hP : Clique g' P)
    (hTP : Clique g (x :: P) → TriP g (x :: P)) : TriP g' P := by
  have hk := c.ker
  -- `x :: P` is a clique of `g`
  have hxQ : x ∈ x :: P := List.mem_cons_self
  have ownQ_of : ∀ p nh n, g'.node? p = some nh → g.node? p = some n → OwnsAll P nh → OwnsAll (x :: P) n := by
    intro p nh n hnh hn hown q hq
    obtain ⟨hxn, hiff⟩ := hE1 p nh n hnh hn
    rcases List.mem_cons.mp hq with he | hq
    · rw [he]; exact hxn
    · exact ((hiff q).mp (hown q hq)).1
  have hQ : Clique g (x :: P) := by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · rw [he]
      refine ⟨nx, hx, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with he' | hp
      · rw [he']; exact self_own_pc c x nx hx
      · obtain ⟨nhp, hnhp, _⟩ := hP p hp
        obtain ⟨np, hnp⟩ := hE0 p nhp hnhp
        exact hk.sym p np x nx hnp hx (hE1 p nhp np hnhp hnp).1
    · obtain ⟨nhq, hnhq, hownq⟩ := hP q hq
      obtain ⟨nq, hnq⟩ := hE0 q nhq hnhq
      exact ⟨nq, hnq, ownQ_of q nhq nq hnhq hnq hownq⟩
  have hTQ := hTP hQ
  -- membership in a table of `g'`
  have mem' : ∀ z nhz nz v nv, g'.node? z = some nhz → g.node? z = some nz → g.node? v = some nv →
      x ∈ nv.owners → CxP g (x :: P) nz v → v ∈ nhz.owners := by
    intro z nhz nz v nv hnhz hnz hnv hxv hC
    have hvz : v ∈ nz.owners := by obtain ⟨_, _, h, _⟩ := hC; exact h
    exact ((hE1 z nhz nz hnhz hnz).2 v).mpr ⟨hvz, inS_of hnv hxv, cx_of_cxP c hx hxQ hC⟩
  -- a node of `g` owning `x :: P`, reached by a compatible link, is a node of `g'` owning `P`
  have node' : ∀ (nz : PNodeM) v nv, g.node? v = some nv → OwnsAll (x :: P) nv → CxP g (x :: P) nz v →
      ∃ nhv, g'.node? v = some nhv ∧ OwnsAll P nhv := by
    intro nz v nv hnv hvQ hC
    obtain ⟨nhv, hnhv⟩ := hE2 v nv hnv (hvQ x hxQ)
    refine ⟨nhv, hnhv, fun p hp => ?_⟩
    obtain ⟨nhp, hnhp, _⟩ := hP p hp
    obtain ⟨np, hnp⟩ := hE0 p nhp hnhp
    have hxp : x ∈ np.owners := (hE1 p nhp np hnhp hnp).1
    exact ((hE1 v nhv nv hnhv hnv).2 p).mpr ⟨hvQ p (List.mem_cons_of_mem _ hp), inS_of hnp hxp,
      cx_member c hx hxQ hnv hvQ hC p np hnp (List.mem_cons_of_mem _ hp)⟩
  -- a compatible link of `g` between nodes owning `x :: P` is a `P`-compatible link of `g'`
  have link' : ∀ z nhz nz v nv, g'.node? z = some nhz → g.node? z = some nz → OwnsAll (x :: P) nz →
      g.node? v = some nv → OwnsAll (x :: P) nv → CxP g (x :: P) nz v → CxP g' P nhz v := by
    intro z nhz nz v nv hnhz hnz hzQ hnv hvQ hC
    obtain ⟨nhv, hnhv, _⟩ := node' nz v nv hnv hvQ hC
    refine ⟨nhv, hnhv, mem' z nhz nz v nv hnhz hnz hnv (hvQ x hxQ) hC, fun l h0 h1 => ?_⟩
    rw [hcs] at h1
    obtain ⟨s, hs, hsv, hss, ⟨ns, hns, hsQ⟩, czs, cvs⟩ := hTQ z nz v nv hnz hnv hzQ hvQ hC l h0 h1
    obtain ⟨nhs, hnhs, hsP⟩ := node' nz s ns hns hsQ czs
    exact ⟨s, mem' z nhz nz s ns hnhz hnz hns (hsQ x hxQ) czs,
      mem' v nhv nv s ns hnhv hnv hns (hsQ x hxQ) cvs, hss, nhs, hnhs, hsP⟩
  -- the pair rule of `g'` relative to `P`
  intro y nhy w nhw hy' hw' hyP hwP hC l h0 h1
  obtain ⟨ny, hny⟩ := hE0 y nhy hy'
  obtain ⟨nw, hnw⟩ := hE0 w nhw hw'
  have hyQ := ownQ_of y nhy ny hy' hny hyP
  have hwQ := ownQ_of w nhw nw hw' hnw hwP
  -- the link, seen in `g`
  have hCg : CxP g (x :: P) ny w := by
    obtain ⟨nhw', hnhw', hwy, hl⟩ := hC
    rw [hw'] at hnhw'; cases hnhw'
    refine ⟨nw, hnw, ((hE1 y nhy ny hy' hny).2 w).mp hwy |>.1, fun l' h0' h1' => ?_⟩
    obtain ⟨r, hr, hrw, hrs, nhr, hnhr, hrP⟩ := hl l' h0' (by rw [hcs]; exact h1')
    obtain ⟨nr, hnr⟩ := hE0 r nhr hnhr
    exact ⟨r, ((hE1 y nhy ny hy' hny).2 r).mp hr |>.1, ((hE1 w nhw nw hw' hnw).2 r).mp hrw |>.1, hrs,
      nr, hnr, ownQ_of r nhr nr hnhr hnr hrP⟩
  rw [hcs] at h1
  obtain ⟨r, _, _, hrs, ⟨nr, hnr, hrQ⟩, cy, cw⟩ := hTQ y ny w nw hny hnw hyQ hwQ hCg l h0 h1
  exact ⟨r, mem' y nhy ny r nr hy' hny hnr (hrQ x hxQ) cy, mem' w nhw nw r nr hw' hnw hnr (hrQ x hxQ) cw,
    hrs, node' ny r nr hnr hrQ cy, link' y nhy ny r nr hy' hny hyQ hnr hrQ cy,
    link' w nhw nw r nr hw' hnw hwQ hnr hrQ cw⟩

/-- **`CliqueTri` passes to a state with the cut tables of `x`.** -/
theorem cliqueTri_of_cut {g g' : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx)
    (hE0 : ∀ p nh, g'.node? p = some nh → ∃ n, g.node? p = some n)
    (hE1 : ∀ p nh n, g'.node? p = some nh → g.node? p = some n →
      x ∈ n.owners ∧ ∀ q, q ∈ nh.owners ↔ (q ∈ n.owners ∧ inS g x q = true ∧ Cx g x n q))
    (hE2 : ∀ p n, g.node? p = some n → x ∈ n.owners → ∃ nh, g'.node? p = some nh)
    (hcs : g'.current_step = g.current_step) (hT : CliqueTri g) : CliqueTri g' :=
  fun P hP => triP_of_cut c x nx hx hE0 hE1 hE2 hcs P hP (fun hQ => hT (x :: P) hQ)

-- ============================================================
-- The pin is the cut sub-kernel
-- ============================================================

section
variable {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId)
  (hx : x ∈ ownersAt g.gowners k) (hk' : Kernel (filterAll g [x.id]))
include c hp hx hk'

/-- After the pin, every table holds `x`. -/
theorem pin_owns_x (p : PathNodeId) (nh : PNodeM) (hnh : (filterAll g [x.id]).node? p = some nh) :
    x ∈ nh.owners := by
  obtain ⟨hxg, hxs'⟩ := List.mem_filter.mp hx
  have hxs : x.id.step = k := eq_of_beq hxs'
  have hb := KernelIff.below_filterAll_self g c.pc.nd [x.id]
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn x hxg)
  have hxm := List.mem_of_find?_eq_some hnx
  have hxid : nx.id = x := node?_id_eq g x nx hnx
  have h0 : 0 ≤ x.id.step := by have := c.pc.snn nx hxm; rw [hxid] at this; exact this
  have h1 : x.id.step < g.current_step := by have := c.pc.below nx hxm; rw [hxid] at this; exact this
  have hv := ((isValidNode_iff _ nh).mp (hk'.valid p nh hnh)).1
  rw [← hb.step] at hv
  obtain ⟨e, he, hes⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv x.id.step (mem_intRange h0 (by omega)))
  have hes' : e.id.step = x.id.step := eq_of_beq hes
  have heg' := hk'.own p nh hnh e he
  have hid : e.id = x.id := ReaderPrefix.ownersAt_pin g x e (mem_ownersAt heg' hes')
  have heg := hb.gow e heg'
  have : e = x := gowner_eq c hp e x heg hxg (by rw [hes']; exact h0) (by rw [hes', hxs]; exact Int.le_refl k) hid
  rw [← this]; exact he

/-- **The pinned state sits inside the cut sub-kernel.** -/
theorem below_cut_pin : Below (restrictPin₁ g x) (filterAll g [x.id]) := by
  have hb := KernelIff.below_filterAll_self g c.pc.nd [x.id]
  have hk := c.pc.ker
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (hk.gn x (List.mem_filter.mp hx).1)
  -- a node of the pinned state, seen in `g`
  have down : ∀ q nhq, (filterAll g [x.id]).node? q = some nhq →
      ∃ nq, g.node? q = some nq ∧ x ∈ nq.owners ∧ ∀ v ∈ nhq.owners, v ∈ nq.owners := by
    intro q nhq hnhq
    obtain ⟨nq, hnq, ho, _, _⟩ := hb.node q nhq hnhq
    exact ⟨nq, hnq, ho x (pin_owns_x c hp x hx hk' q nhq hnhq), ho⟩
  -- a table entry of the pinned state is kept by the cut
  have kept : ∀ p nh n, (filterAll g [x.id]).node? p = some nh → g.node? p = some n →
      (∀ v ∈ nh.owners, v ∈ n.owners) → ∀ q ∈ nh.owners, q ∈ n.owners.filter (keep g x n) := by
    intro p nh n hnh hn ho q hq
    obtain ⟨nhq, hnhq⟩ := hk'.isNode_owner p nh hnh q hq
    obtain ⟨nq, hnq, hxq, hoq⟩ := down q nhq hnhq
    refine mem_keep (ho q hq) (inS_of hnq hxq) ⟨nq, nx, hnq, hnx, ho q hq, fun l h0 h1 => ?_⟩
    rw [hb.step] at h1
    obtain ⟨r, hr, hrq, hrs⟩ := hk'.pair p nh q nhq hnh hnhq hq l h0 h1
    obtain ⟨nhr, hnhr⟩ := hk'.isNode_owner p nh hnh r hr
    obtain ⟨nr, hnr, hxr, _⟩ := down r nhr hnhr
    exact ⟨r, ho r hr, hoq r hrq, hk.sym r nr x nx hnr hnx hxr, hrs⟩
  refine ⟨hb.step, fun q hq => ?_, fun p nh hnh => ?_⟩
  · obtain ⟨nhq, hnhq⟩ := Option.isSome_iff_exists.mp (hk'.gn q hq)
    obtain ⟨nq, hnq, hxq, _⟩ := down q nhq hnhq
    exact List.mem_filter.mpr ⟨hb.gow q hq, inS_of hnq hxq⟩
  · obtain ⟨n, hn, ho, hpa, hso⟩ := hb.node p nh hnh
    have hxn : x ∈ n.owners := ho x (pin_owns_x c hp x hx hk' p nh hnh)
    refine ⟨rn₁ g x n, restrict₁_node? c.pc.nd p n hn hxn, kept p nh n hnh hn ho, fun q hq => ?_,
      fun q hq => ?_⟩
    · have := kept p nh n hnh hn ho q (hk'.linkP p nh hnh q hq).1
      obtain ⟨_, hk2⟩ := List.mem_filter.mp this
      exact List.mem_filter.mpr ⟨hpa q hq, hk2⟩
    · have := kept p nh n hnh hn ho q (hk'.linkS p nh hnh q hq).1
      obtain ⟨_, hk2⟩ := List.mem_filter.mp this
      exact List.mem_filter.mpr ⟨hso q hq, hk2⟩
end

/-- **The pin is the cut sub-kernel**: under `TriPin₁ g x`, the pinned state and `restrictPin₁ g x`
sit inside each other. -/
theorem pin_eq_cut {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId)
    (hx : x ∈ ownersAt g.gowners k) (hk' : Kernel (filterAll g [x.id])) (ht : TriPin₁ g x) :
    Below (restrictPin₁ g x) (filterAll g [x.id]) ∧ Below (filterAll g [x.id]) (restrictPin₁ g x) := by
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn x (List.mem_filter.mp hx).1)
  obtain ⟨hK, _, hbK, hpin⟩ := restrict₁_kernel c.pc x nx hnx ht
  refine ⟨below_cut_pin c hp x hx hk', ?_⟩
  exact below_filterAll hK hbK [x.id]
    (fun r hr q hq hqs => by rw [List.mem_singleton.mp hr] at hqs ⊢; exact hpin q hq hqs)

/-- **Under `TriPin₁ g x`, the pinned state has exactly the cut tables of `x`**, in the form
`triP_of_cut` reads. -/
theorem pin_cut_facts {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId)
    (hx : x ∈ ownersAt g.gowners k) (hk' : Kernel (filterAll g [x.id])) (ht : TriPin₁ g x) :
    (∀ p nh, (filterAll g [x.id]).node? p = some nh → ∃ n, g.node? p = some n) ∧
    (∀ p nh n, (filterAll g [x.id]).node? p = some nh → g.node? p = some n →
      x ∈ n.owners ∧ ∀ q, q ∈ nh.owners ↔ (q ∈ n.owners ∧ inS g x q = true ∧ Cx g x n q)) ∧
    (∀ p n, g.node? p = some n → x ∈ n.owners → ∃ nh, (filterAll g [x.id]).node? p = some nh) ∧
    (filterAll g [x.id]).current_step = g.current_step := by
  obtain ⟨hin, hout⟩ := pin_eq_cut c hp x hx hk' ht
  have hb := KernelIff.below_filterAll_self g c.pc.nd [x.id]
  refine ⟨fun p nh hnh => ?_, fun p nh n hnh hn => ?_, fun p n hn hxn => ?_, hb.step.symm⟩
  · obtain ⟨n, hn, _⟩ := hb.node p nh hnh
    exact ⟨n, hn⟩
  · obtain ⟨nk, hnk, ho, _, _⟩ := hin.node p nh hnh
    obtain ⟨n', hn', hxn', hEq⟩ := restrict₁_node?_inv c.pc.nd p nk hnk
    rw [hn] at hn'; cases hn'
    subst hEq
    obtain ⟨nh2, hnh2, ho2, _, _⟩ := hout.node p (rn₁ g x n) (restrict₁_node? c.pc.nd p n hn hxn')
    rw [hnh] at hnh2; cases hnh2
    exact ⟨hxn', fun q => ⟨fun hq => mem_keep_of (ho q hq), fun ⟨h1, h2, h3⟩ => ho2 q (mem_keep h1 h2 h3)⟩⟩
  · obtain ⟨nh, hnh, _⟩ := hout.node p (rn₁ g x n) (restrict₁_node? c.pc.nd p n hn hxn)
    exact ⟨nh, hnh⟩

/-- **The pin keeps `CliqueTri`.** -/
theorem cliqueTri_pin {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId)
    (hx : x ∈ ownersAt g.gowners k) (hk' : Kernel (filterAll g [x.id])) (hT : CliqueTri g) :
    CliqueTri (filterAll g [x.id]) := by
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn x (List.mem_filter.mp hx).1)
  have ht := allTriPin₁_of_cliqueTri c.pc hT x nx hnx
  obtain ⟨e0, e1, e2, ecs⟩ := pin_cut_facts c hp x hx hk' ht
  exact cliqueTri_of_cut c.pc x nx hnx e0 e1 e2 ecs hT

-- ============================================================
-- With the reader: only the starting states matter
-- ============================================================

variable (φ : Cnf)

/-- **Along the reader, `CliqueTri` at the start is enough.** -/
theorem cliqueTri_reader (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (h0 : isValid (filterAll kv.2 []) = true → CliqueTri (filterAll kv.2 [])) :
    ∀ ps g, ReadPins (filterAll kv.2 []) ps g → isValid g = true → CliqueTri g := by
  intro ps g hp
  induction hp with
  | start => exact h0
  | pin g k q ps hp hv hf hq hv' ih =>
    intro _
    have c := aCtx_readPins φ hbd kv hkv ps g hp hv
    have hk' := KernelReader.kernel_readPins φ hbd kv hkv (q.id :: ps) _
      (ReadPins.pin g k q ps hp hv hf hq hv') hv'
    exact cliqueTri_pin c (prefixUpTo_firstChoice g k hf) q hq hk' (ih hv)

/-- **The reader decides `φ` when every valid starting state satisfies `CliqueTri`.** -/
theorem readerVerdictW_iff_of_cliqueTri (hbd : Bounded φ)
    (h0 : ∀ kv ∈ pureRun φ, isValid (filterAll kv.2 []) = true → CliqueTri (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_allTriPin₁ φ hbd (fun kv hkv g hF hv => ?_)
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  exact allTriPin₁_of_cliqueTri (pinCtx_readPins φ hbd kv hkv ps g hp hv)
    (cliqueTri_reader φ hbd kv hkv (h0 kv hkv) ps g hp hv)

/-- info: 'AbsSatBin.GraphPath.Model.CliqueTri.cliqueTri_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cliqueTri_pin

/-- info: 'AbsSatBin.GraphPath.Model.CliqueTri.readerVerdictW_iff_of_cliqueTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_cliqueTri

end AbsSatBin.GraphPath.Model.CliqueTri
