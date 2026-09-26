-- lean/improves_bin/AbsSatBin/GraphPath/Model/AmbHighCore.lean
import AbsSatBin.GraphPath.Model.AmbTriCore

/-!
# `AmbFar ⇐ AmbHigh`: forced nodes own everything

Let `k` be the reader's first choice. Below `k` every step has a single live path node
(`AmbTriCore.gowner_eq`). Such a **forced** node is in every table: every live node has an entry at
its step, and that entry can only be it (`forced_in_all`). By symmetry, **its own table holds every
live node** (`forced_owns_all`).

So a pair of `AmbFar` with a member below `k` always shares: the pair rule of the other member (or of
`x` itself) against `x` gives the entry, and the forced member owns it. What is left is
**`AmbHigh g k x`**: both members at steps `≥ k + 3`, at steps `l > k`. The triples lie entirely above
the fixed prefix.
-/

namespace AbsSatBin.GraphPath.Model.AmbHighCore

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCore
open AbsSatBin.GraphPath.Model.AmbTriCore
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

variable {g : GPathM}

-- ============================================================
-- Forced nodes
-- ============================================================

/-- **A node below the choice is in every table.** -/
theorem forced_in_all (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (hlo : y.id.step < k) (q : PathNodeId) (nq : PNodeM)
    (hq : g.node? q = some nq) : y ∈ nq.owners := by
  have hym := List.mem_of_find?_eq_some hy
  have hyid : ny.id = y := node?_id_eq g y ny hy
  have h0 : 0 ≤ y.id.step := by have := c.pc.snn ny hym; rw [hyid] at this; exact this
  have h1 : y.id.step < g.current_step := by have := c.pc.below ny hym; rw [hyid] at this; exact this
  have hyg := c.pc.ker.gow y ny hy
  obtain ⟨r, hr, hrs⟩ := entry_at c q nq hq y.id.step h0 h1
  have hrg := c.pc.ker.own q nq hq r hr
  have hid := ids_eq_of_choiceAt g y.id.step (hp y.id.step h0 hlo) r y (mem_ownersAt hrg hrs)
    (mem_ownersAt hyg rfl)
  have e : r = y := gowner_eq c hp r y hrg hyg (by rw [hrs]; exact h0)
    (by rw [hrs]; exact Int.le_of_lt hlo) hid
  rw [← e]; exact hr

/-- **A node below the choice owns every live node.** -/
theorem forced_owns_all (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (hlo : y.id.step < k) (r : PathNodeId) (hr : r ∈ g.gowners) :
    r ∈ ny.owners := by
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn r hr)
  exact c.pc.ker.sym r nr y ny hnr hy (forced_in_all c hp y ny hy hlo r nr hnr)

-- ============================================================
-- What is left
-- ============================================================

/-- **`AmbHigh`**: ambiguous pairs with both members from `k + 3` on, at steps above the choice. -/
def AmbHigh (g : GPathM) (k : Int) (x : PathNodeId) : Prop :=
  ∀ y ny w nw nx, g.node? y = some ny → g.node? w = some nw → g.node? x = some nx →
    x ∈ ny.owners → x ∈ nw.owners → w ∈ ny.owners → excl x ny = false → excl x nw = false →
    -- idx: above the three-step window (one gpath row per map step, bin map too)
    k + 3 ≤ y.id.step → k + 3 ≤ w.id.step →
    ∀ l, k < l → l < g.current_step → ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l

/-- **`AmbFar ⇐ AmbHigh`**. -/
theorem ambFar_of_ambHigh (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (hk0 : 0 ≤ k) (x : PathNodeId)
    (h : AmbHigh g k x) : AmbFar g k x := by
  intro y ny w nw nx hy hw hxn hxy hxw hwy ey ew hyf hwf l hl h1
  have h0 : 0 ≤ l := Int.le_of_lt (Int.lt_of_le_of_lt hk0 hl)
  rcases hyf with hyl | hyh
  · -- `y` is forced: the pair rule of `w` against `x`
    obtain ⟨r, hrw, hrx, hrs⟩ := c.pc.ker.pair w nw x nx hw hxn hxw l h0 h1
    exact ⟨r, forced_owns_all c hp y ny hy hyl r (c.pc.ker.own w nw hw r hrw), hrw, hrx, hrs⟩
  · rcases hwf with hwl | hwh
    · -- `w` is forced: the pair rule of `y` against `x`
      obtain ⟨r, hry, hrx, hrs⟩ := c.pc.ker.pair y ny x nx hy hxn hxy l h0 h1
      exact ⟨r, hry, forced_owns_all c hp w nw hw hwl r (c.pc.ker.own y ny hy r hry), hrx, hrs⟩
    · exact h y ny w nw nx hy hw hxn hxy hxw hwy ey ew hyh hwh l hl h1

-- ============================================================
-- With the reader
-- ============================================================

variable (φ : Cnf)

/-- `AmbHigh` at the first choice, along the reader. -/
def AmbHighReader (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, AmbHigh g k q

theorem ambFarReader_of_ambHigh (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ha : AmbHighReader (filterAll kv.2 [])) : AmbFarReader (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨q, hq, hqa⟩ := ha g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := aCtx_readPins φ hbd kv hkv ps g hp hv
  have hk0 : 0 ≤ k := by
    unfold firstChoice at hf
    exact mem_intRange_lower (List.mem_of_find?_eq_some hf)
  exact ⟨q, hq, ambFar_of_ambHigh c (prefixUpTo_firstChoice g k hf) hk0 q hqa⟩

/-- **The reader decides `φ` when, at every valid state it visits, some node of the first choice
satisfies the triple rule on the ambiguous pairs above its window.** -/
theorem readerVerdictW_iff_of_ambHigh (hbd : Bounded φ)
    (ha : ∀ kv ∈ pureRun φ, AmbHighReader (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_ambFar φ hbd (fun kv hkv => ambFarReader_of_ambHigh φ hbd kv hkv (ha kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.AmbHighCore.ambFar_of_ambHigh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ambFar_of_ambHigh

/-- info: 'AbsSatBin.GraphPath.Model.AmbHighCore.readerVerdictW_iff_of_ambHigh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_ambHigh

end AbsSatBin.GraphPath.Model.AmbHighCore
