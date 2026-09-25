-- lean/improves_bin/AbsSatBin/GraphPath/Model/TriPinCore.lean
import AbsSatBin.GraphPath.Model.KernelIff

/-!
# What is under `TriPin`: only ambiguous pairs can break it

Let `x` be a live node of a kernel. A node `y` that owns `x` is **exclusive** to `x` when `x` is the
only entry of its table at `x`'s step.

* **`tri_of_exclusive`**: if `y` (or `w`) is exclusive, the triple `(y, w, x)` shares an entry at every
  step. The pair rule of `y` and `w` gives a common entry `r`; the pair rule of `y` (or `w`) and `r`
  at `x`'s step can only meet at `x`, so `r` owns `x`, and by symmetry `x` owns `r`.
* **`triPin_of_ambTri`**: so `TriPin g x` only asks about **ambiguous pairs**: two nodes that own each
  other, both own `x`, and both also own another node of `x`'s step.

On the bin map the other node of `x`'s step is the other bit. A failure of `TriPin` at `x` is then
two nodes, each compatible with both bits, that own each other but whose common entries at some step
are all incompatible with `x`. This cannot follow from the kernel's local axioms alone (they admit
fixpoints without any chain); it has to come from how the machine built the tables.
-/

namespace AbsSatBin.GraphPath.Model.TriPinCore

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit

/-- `x` is the only entry of the table at `x`'s step. -/
def Exclusive (x : PathNodeId) (ny : PNodeM) : Prop := ∀ q ∈ ny.owners, q.id.step = x.id.step → q = x

/-- **An exclusive member makes the triple share.** -/
theorem tri_of_exclusive {g : GPathM} (c : PinCtx g) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (w : PathNodeId) (nw : PNodeM) (hw : g.node? w = some nw) (hwy : w ∈ ny.owners)
    (hex : Exclusive x ny ∨ Exclusive x nw) (l : Int) (h0 : 0 ≤ l) (h1 : l < g.current_step) :
    ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l := by
  have hk := c.ker
  have hxm := List.mem_of_find?_eq_some hx
  have hxid : nx.id = x := node?_id_eq g x nx hx
  have hx0 : 0 ≤ x.id.step := by have := c.snn nx hxm; rw [hxid] at this; exact this
  have hx1 : x.id.step < g.current_step := by have := c.below nx hxm; rw [hxid] at this; exact this
  obtain ⟨r, hry, hrw, hrs⟩ := hk.pair y ny w nw hy hw hwy l h0 h1
  obtain ⟨nr, hnr⟩ := hk.isNode_owner y ny hy r hry
  refine ⟨r, hry, hrw, ?_, hrs⟩
  -- `r` owns `x`: the pair rule with the exclusive member at `x`'s step
  have hxr : x ∈ nr.owners := by
    rcases hex with hex | hex
    · obtain ⟨e, hey, her, hes⟩ := hk.pair y ny r nr hy hnr hry x.id.step hx0 hx1
      rw [← hex e hey hes]; exact her
    · have hrw' : r ∈ nw.owners := hrw
      obtain ⟨e, hew, her, hes⟩ := hk.pair w nw r nr hw hnr hrw' x.id.step hx0 hx1
      rw [← hex e hew hes]; exact her
  exact hk.sym r nr x nx hnr hx hxr

/-- `Exclusive`, as a test. -/
def excl (x : PathNodeId) (ny : PNodeM) : Bool :=
  ny.owners.all (fun q => !(q.id.step == x.id.step) || q == x)

theorem exclusive_of_excl (x : PathNodeId) (ny : PNodeM) (h : excl x ny = true) : Exclusive x ny := by
  intro q hq hs
  have := List.all_eq_true.mp h q hq
  rw [beq_iff_eq.mpr hs, Bool.not_true, Bool.false_or] at this
  exact eq_of_beq this

/-- `TriPin` restricted to ambiguous pairs. -/
def AmbTri (g : GPathM) (x : PathNodeId) : Prop :=
  ∀ y ny w nw nx, g.node? y = some ny → g.node? w = some nw → g.node? x = some nx →
    x ∈ ny.owners → x ∈ nw.owners → w ∈ ny.owners → excl x ny = false → excl x nw = false →
    ∀ l, 0 ≤ l → l < g.current_step → ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l

/-- **`TriPin` only asks about ambiguous pairs.** -/
theorem triPin_of_ambTri {g : GPathM} (c : PinCtx g) (x : PathNodeId) (h : AmbTri g x) : TriPin g x := by
  intro y ny w nw nx hy hw hx hxy hxw hwy l h0 h1
  cases ey : excl x ny with
  | true =>
    exact tri_of_exclusive c x nx hx y ny hy w nw hw hwy (Or.inl (exclusive_of_excl x ny ey)) l h0 h1
  | false =>
    cases ew : excl x nw with
    | true =>
      exact tri_of_exclusive c x nx hx y ny hy w nw hw hwy (Or.inr (exclusive_of_excl x nw ew)) l h0 h1
    | false => exact h y ny w nw nx hy hw hx hxy hxw hwy ey ew l h0 h1

/-- info: 'AbsSatBin.GraphPath.Model.TriPinCore.triPin_of_ambTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triPin_of_ambTri

end AbsSatBin.GraphPath.Model.TriPinCore
