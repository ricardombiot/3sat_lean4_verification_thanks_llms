-- lean/improves_bin/AbsSatBin/GraphPath/Model/OneShot.lean
import AbsSatBin.GraphPath.Model.PrefixTri

/-!
# `TriPin₁` is "one round of cuts": the review after a pin has no cascade

At a reader state, pinning `x` and reviewing always lands **inside** the cut sub-kernel
`restrictPin₁ g x` (`CliqueTri.below_cut_pin`: every table of the pinned state holds `x`, and every link
of it has its witnesses inside). This module shows that `TriPin₁` is exactly the other inclusion:

* **`triPin₁_iff_oneShot`**: `TriPin₁ g x` holds iff the pinned state (a valid kernel) **contains** the
  cut sub-kernel — the review removed the nodes that do not own `x` and the links that are not
  `x`-compatible, **and nothing else**. No cascade: one round of cuts is the whole review.
* So the reader decides `φ` as soon as, at every valid state it visits, some pin at the first choice
  survives with a one-shot review (`readerVerdictW_iff_of_oneShot`).

This is an operational form of the open core: a statement about what the review does after a pin,
checkable on the machine's own objects.
-/

namespace AbsSatBin.GraphPath.Model.OneShot

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCut
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.AmbTriCore
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- The pinned state contains the cut sub-kernel: the review after the pin cut nothing more. -/
def OneShot (g : GPathM) (x : PathNodeId) : Prop := Below (filterAll g [x.id]) (restrictPin₁ g x)

/-- **`TriPin₁` is a one-shot review.** -/
theorem triPin₁_iff_oneShot {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId)
    (hx : x ∈ ownersAt g.gowners k) (hk' : Kernel (filterAll g [x.id])) :
    TriPin₁ g x ↔ OneShot g x := by
  refine ⟨fun ht => (pin_eq_cut c hp x hx hk' ht).2, fun hB => ?_⟩
  have hin := below_cut_pin c hp x hx hk'
  have hb := KernelIff.below_filterAll_self g c.pc.nd [x.id]
  have hk := c.pc.ker
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (hk.gn x (List.mem_filter.mp hx).1)
  -- a table of the pinned state is the cut table
  have back : ∀ z nz, g.node? z = some nz → x ∈ nz.owners → ∀ nhz,
      (filterAll g [x.id]).node? z = some nhz → ∀ r ∈ nhz.owners, r ∈ nz.owners.filter (keep g x nz) := by
    intro z nz hz hxz nhz hnhz r hr
    obtain ⟨nk, hnk, ho, _, _⟩ := hin.node z nhz hnhz
    rw [restrict₁_node? c.pc.nd z nz hz hxz] at hnk; cases hnk
    exact ho r hr
  intro y ny w nw nx' hy hw hx' hxy hxw hC l h0 h1
  rw [hnx] at hx'; cases hx'
  obtain ⟨nhy, hnhy, hoy, _, _⟩ := hB.node y (rn₁ g x ny) (restrict₁_node? c.pc.nd y ny hy hxy)
  obtain ⟨nhw, hnhw, _, _, _⟩ := hB.node w (rn₁ g x nw) (restrict₁_node? c.pc.nd w nw hw hxw)
  have hwy0 : w ∈ ny.owners := by obtain ⟨_, _, _, _, h, _⟩ := hC; exact h
  have hwy : w ∈ nhy.owners := hoy w (mem_keep hwy0 (inS_of hw hxw) hC)
  obtain ⟨r, hr, hrw, hrs⟩ := hk'.pair y nhy w nhw hnhy hnhw hwy l h0 (by rw [← hb.step]; exact h1)
  obtain ⟨hry, hrS, hcy⟩ := mem_keep_of (back y ny hy hxy nhy hnhy r hr)
  obtain ⟨_, _, hcw⟩ := mem_keep_of (back w nw hw hxw nhw hnhw r hrw)
  have hrw' : r ∈ nw.owners := (mem_keep_of (back w nw hw hxw nhw hnhw r hrw)).1
  obtain ⟨nr, hnr, hxr⟩ := of_inS hrS
  exact ⟨r, hry, hrw', hk.sym r nr x nx hnr hnx hxr, hrs, hcy, hcw⟩

-- ============================================================
-- Where the cut can act: only at merges
-- ============================================================

/-- **A node with a single parent keeps its link to it**: its table lies inside the parent's
(the kernel's neighbour clause), so the pair rule against `x` already gives `x`-compatible witnesses. -/
theorem cx_unique_parent {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (hxy : x ∈ ny.owners) (h1 : 1 ≤ y.id.step) (r : PathNodeId) (hr : r ∈ ny.parents)
    (huniq : ∀ c' ∈ ny.parents, c' = r) : Cx g x ny r := by
  have hk := c.ker
  obtain ⟨hry, nr, hnr, _⟩ := hk.linkP y ny hy r hr
  -- the table of `y` lies inside the table of `r`
  have hsub : ∀ v ∈ ny.owners, v ∈ nr.owners := by
    intro v hv
    obtain ⟨c', hc', nc', hnc', hvc⟩ := hk.nbrP y ny hy h1 v hv
    rw [huniq c' hc', hnr] at hnc'; cases hnc'
    exact hvc
  refine ⟨nr, nx, hnr, hx, hry, fun l h0 h1' => ?_⟩
  obtain ⟨s, hs, hsx, hss⟩ := hk.pair y ny x nx hy hx hxy l h0 h1'
  exact ⟨s, hs, hsub s hs, hsx, hss⟩

/-- **A node that is the single parent of a son keeps its link to it.** -/
theorem cx_unique_son {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (s : PathNodeId) (ns : PNodeM) (hs : g.node? s = some ns) (hxs : x ∈ ns.owners)
    (h1 : 1 ≤ s.id.step) (hys : y ∈ ns.parents) (huniq : ∀ c' ∈ ns.parents, c' = y) : Cx g x ny s := by
  have hk := c.ker
  have hsy : s ∈ ny.owners := by
    obtain ⟨hyo, ny', hny', hsy⟩ := hk.linkP s ns hs y hys
    rw [hy] at hny'; cases hny'; exact hsy
  have hsub : ∀ v ∈ ns.owners, v ∈ ny.owners := by
    intro v hv
    obtain ⟨c', hc', nc', hnc', hvc⟩ := hk.nbrP s ns hs h1 v hv
    rw [huniq c' hc', hy] at hnc'; cases hnc'
    exact hvc
  refine ⟨ns, nx, hs, hx, hsy, fun l h0 h1' => ?_⟩
  obtain ⟨t, ht, htx, hts⟩ := hk.pair s ns x nx hs hx hxs l h0 h1'
  exact ⟨t, hsub t ht, ht, htx, hts⟩

-- ============================================================
-- How compatibility moves along the links
-- ============================================================

/-- **Compatibility is monotone in the far end's table**: a link to `r` that is `x`-compatible stays
`x`-compatible when `r` is replaced by a node `r'` whose table contains `r`'s. -/
theorem cx_mono {g : GPathM} (c : PinCtx g) (x : PathNodeId) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (r : PathNodeId) (r' : PathNodeId) (nr' : PNodeM) (hnr' : g.node? r' = some nr')
    (hsub : ∀ nr, g.node? r = some nr → ∀ v ∈ nr.owners, v ∈ nr'.owners) (h : Cx g x ny r) :
    Cx g x ny r' := by
  obtain ⟨nr, nx, hnr, hx, hry, hl⟩ := h
  have hyr : y ∈ nr.owners := c.ker.sym y ny r nr hy hnr hry
  refine ⟨nr', nx, hnr', hx, c.ker.sym r' nr' y ny hnr' hy (hsub nr hnr y hyr), fun l h0 h1 => ?_⟩
  obtain ⟨s, hs, hsr, hsx, hss⟩ := hl l h0 h1
  exact ⟨s, hs, hsub nr hnr s hsr, hsx, hss⟩

/-- The table of a node with a single parent lies inside the parent's. -/
theorem table_sub_unique_parent {g : GPathM} (c : PinCtx g) (r : PathNodeId) (nr : PNodeM)
    (hnr : g.node? r = some nr) (h1 : 1 ≤ r.id.step) (r' : PathNodeId) (nr' : PNodeM)
    (hnr' : g.node? r' = some nr') (huniq : ∀ c' ∈ nr.parents, c' = r') :
    ∀ v ∈ nr.owners, v ∈ nr'.owners := by
  intro v hv
  obtain ⟨c', hc', nc', hnc', hvc⟩ := c.ker.nbrP r nr hnr h1 v hv
  rw [huniq c' hc', hnr'] at hnc'; cases hnc'
  exact hvc

/-- **Compatibility climbs to a single parent**: if `r` has a single parent `r'`, every link to `r` that
is `x`-compatible gives an `x`-compatible link to `r'`. Read backwards: **a cut at `r'` propagates to
its single-parent sons.** -/
theorem cx_to_unique_parent {g : GPathM} (c : PinCtx g) (x : PathNodeId) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (r : PathNodeId) (nr : PNodeM) (hnr : g.node? r = some nr)
    (h1 : 1 ≤ r.id.step) (r' : PathNodeId) (nr' : PNodeM) (hnr' : g.node? r' = some nr')
    (huniq : ∀ c' ∈ nr.parents, c' = r') (h : Cx g x ny r) : Cx g x ny r' :=
  cx_mono c x y ny hy r r' nr' hnr' (fun nr₀ hnr₀ => by
    rw [hnr] at hnr₀; cases hnr₀
    exact table_sub_unique_parent c r nr hnr h1 r' nr' hnr' huniq) h

-- ============================================================
-- Localization: `TriPin₁` can only fail across merges
-- ============================================================

/-- `a` is reached from `y` by going down through single parents. -/
inductive UDesc (g : GPathM) : PathNodeId → PathNodeId → Prop where
  | refl (y : PathNodeId) : UDesc g y y
  | step (y r a : PathNodeId) (nr : PNodeM) : UDesc g y r → g.node? r = some nr → 1 ≤ r.id.step →
      a ∈ nr.parents → (∀ c' ∈ nr.parents, c' = a) → UDesc g y a

section
variable {g : GPathM} (c : PinCtx g)
include c

theorem udesc_node {y a : PathNodeId} (h : UDesc g y a) (ny : PNodeM) (hy : g.node? y = some ny) :
    ∃ na, g.node? a = some na := by
  induction h with
  | refl => exact ⟨ny, hy⟩
  | step r a nr _ hnr _ ha _ _ =>
    obtain ⟨_, na, hna, _⟩ := c.ker.linkP r nr hnr a ha
    exact ⟨na, hna⟩

/-- Going down through single parents, tables only grow. -/
theorem udesc_sub {y a : PathNodeId} (h : UDesc g y a) (ny : PNodeM) (hy : g.node? y = some ny)
    (na : PNodeM) (hna : g.node? a = some na) : ∀ v ∈ ny.owners, v ∈ na.owners := by
  induction h generalizing na with
  | refl => rw [hy] at hna; cases hna; exact fun v hv => hv
  | step r a nr hd hnr h1 ha hu ih =>
    exact fun v hv => table_sub_unique_parent c r nr hnr h1 a na hna hu v (ih nr hnr v hv)

/-- The entry of `y`'s table at the step of `a` is `a` itself. -/
theorem udesc_entry {y a : PathNodeId} (h : UDesc g y a) (ny : PNodeM) (hy : g.node? y = some ny)
    (na : PNodeM) (hna : g.node? a = some na) (e : PathNodeId) (he : e ∈ ny.owners)
    (hes : e.id.step = a.id.step) : e = a := by
  have hea := udesc_sub c h ny hy na hna e he
  have hid : na.id = a := node?_id_eq g a na hna
  have := c.oos na (List.mem_of_find?_eq_some hna) e hea (by rw [hid, hes])
  rw [hid] at this; exact this

/-- **Below a node, along single parents, its ancestor is a good witness.** -/
theorem tri_below (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) (y : PathNodeId)
    (ny : PNodeM) (hy : g.node? y = some ny) (hxy : x ∈ ny.owners) (w : PathNodeId) (nw : PNodeM)
    (hw : g.node? w = some nw) (hC : Cx g x ny w) (a : PathNodeId) (hd : UDesc g y a)
    (h0 : 0 ≤ a.id.step) (h1 : a.id.step < g.current_step) :
    a ∈ ny.owners ∧ a ∈ nw.owners ∧ a ∈ nx.owners ∧ Cx g x ny a ∧ Cx g x nw a := by
  obtain ⟨na, hna⟩ := udesc_node c hd ny hy
  have hsub := udesc_sub c hd ny hy na hna
  have hCyw := cx_symm c hy hw hC
  obtain ⟨nw₁, nx₁, hw₁, hx₁, _, hl⟩ := hC
  rw [hw] at hw₁; cases hw₁
  rw [hx] at hx₁; cases hx₁
  obtain ⟨e, he, hew, hex, hes⟩ := hl a.id.step h0 h1
  have hea : e = a := udesc_entry c hd ny hy na hna e he hes
  rw [hea] at he hew hex
  have hsub' : ∀ nr, g.node? y = some nr → ∀ v ∈ nr.owners, v ∈ na.owners := by
    intro nr hnr; rw [hy] at hnr; cases hnr; exact hsub
  exact ⟨he, hew, hex, cx_mono c x y ny hy y a na hna hsub' (cx_self c hx hy hxy),
    cx_mono c x w nw hw y a na hna hsub' hCyw⟩

/-- **Above two nodes, a witness that goes down through single parents to both is good.** -/
theorem tri_above (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) (y : PathNodeId)
    (ny : PNodeM) (hy : g.node? y = some ny) (w : PathNodeId) (nw : PNodeM) (hw : g.node? w = some nw)
    (e : PathNodeId) (ne : PNodeM) (hne : g.node? e = some ne) (hey : e ∈ ny.owners) (hew : e ∈ nw.owners)
    (hex : e ∈ nx.owners) (hdy : UDesc g e y) (hdw : UDesc g e w) : Cx g x ny e ∧ Cx g x nw e := by
  have hk := c.ker
  have hxe : x ∈ ne.owners := hk.sym x nx e ne hx hne hex
  have sy := udesc_sub c hdy ne hne ny hy
  have sw := udesc_sub c hdw ne hne nw hw
  refine ⟨⟨ne, nx, hne, hx, hey, fun l h0 h1 => ?_⟩, ⟨ne, nx, hne, hx, hew, fun l h0 h1 => ?_⟩⟩
  · obtain ⟨s, hs, hsx, hss⟩ := hk.pair e ne x nx hne hx hxe l h0 h1
    exact ⟨s, sy s hs, hs, hsx, hss⟩
  · obtain ⟨s, hs, hsx, hss⟩ := hk.pair e ne x nx hne hx hxe l h0 h1
    exact ⟨s, sw s hs, hs, hsx, hss⟩

/-- **A failure of `TriPin₁` is separated by merges from both ends**: if no good witness exists for the
pair `(y, w)` at step `l`, then neither `y` nor `w` goes down through single parents to step `l`, and no
`x`-witness at `l` goes down through single parents to both. -/
theorem fail_is_merge_separated (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) (y : PathNodeId)
    (ny : PNodeM) (hy : g.node? y = some ny) (hxy : x ∈ ny.owners) (w : PathNodeId) (nw : PNodeM)
    (hw : g.node? w = some nw) (hxw : x ∈ nw.owners) (hC : Cx g x ny w) (l : Int) (h0 : 0 ≤ l)
    (h1 : l < g.current_step)
    (hfail : ¬ ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l ∧ Cx g x ny r ∧ Cx g x nw r) :
    (∀ a, a.id.step = l → ¬ UDesc g y a) ∧ (∀ a, a.id.step = l → ¬ UDesc g w a) ∧
      (∀ e, e.id.step = l → e ∈ ny.owners → e ∈ nw.owners → e ∈ nx.owners → ¬ (UDesc g e y ∧ UDesc g e w)) := by
  refine ⟨fun a has hd => hfail ?_, fun a has hd => hfail ?_, fun e hes hey hew hex ⟨hdy, hdw⟩ => hfail ?_⟩
  · obtain ⟨hay, haw, hax, cy, cw⟩ := tri_below c x nx hx y ny hy hxy w nw hw hC a hd
      (by rw [has]; exact h0) (by rw [has]; exact h1)
    exact ⟨a, hay, haw, hax, has, cy, cw⟩
  · obtain ⟨haw, hay, hax, cw, cy⟩ := tri_below c x nx hx w nw hw hxw y ny hy (cx_symm c hy hw hC) a hd
      (by rw [has]; exact h0) (by rw [has]; exact h1)
    exact ⟨a, hay, haw, hax, has, cy, cw⟩
  · obtain ⟨ne, hne⟩ := c.ker.isNode_owner y ny hy e hey
    obtain ⟨cy, cw⟩ := tri_above c x nx hx y ny hy w nw hw e ne hne hey hew hex hdy hdw
    exact ⟨e, hey, hew, hex, hes, cy, cw⟩
end

-- ============================================================
-- With the reader
-- ============================================================

variable (φ : Cnf)

/-- **At every valid state the reader visits, some pin at the first choice survives with a one-shot
review.** -/
def OneShotReader (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true ∧ OneShot g q

theorem triPin₁Reader_of_oneShot (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (h : OneShotReader (filterAll kv.2 [])) : TriPin₁Reader (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨q, hq, hvq, hos⟩ := h g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := aCtx_readPins φ hbd kv hkv ps g hp hv
  have hk' := KernelReader.kernel_readPins φ hbd kv hkv (q.id :: ps) _
    (ReadPins.pin g k q ps hp hv hf hq hvq) hvq
  exact ⟨q, hq, (triPin₁_iff_oneShot c (prefixUpTo_firstChoice g k hf) q hq hk').mpr hos⟩

/-- **The reader decides `φ` when the review after some pin is one-shot at every state it visits.** -/
theorem readerVerdictW_iff_of_oneShot (hbd : Bounded φ)
    (h : ∀ kv ∈ pureRun φ, OneShotReader (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_triPin₁ φ hbd (fun kv hkv => triPin₁Reader_of_oneShot φ hbd kv hkv (h kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.OneShot.triPin₁_iff_oneShot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triPin₁_iff_oneShot

/-- info: 'AbsSatBin.GraphPath.Model.OneShot.cx_unique_parent' does not depend on any axioms -/
#guard_msgs in
#print axioms cx_unique_parent

/-- info: 'AbsSatBin.GraphPath.Model.OneShot.fail_is_merge_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fail_is_merge_separated

/-- info: 'AbsSatBin.GraphPath.Model.OneShot.readerVerdictW_iff_of_oneShot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_oneShot

end AbsSatBin.GraphPath.Model.OneShot
