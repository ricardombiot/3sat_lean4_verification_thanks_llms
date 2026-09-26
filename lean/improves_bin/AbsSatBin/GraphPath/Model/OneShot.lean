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

/-- info: 'AbsSatBin.GraphPath.Model.OneShot.readerVerdictW_iff_of_oneShot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_oneShot

end AbsSatBin.GraphPath.Model.OneShot
