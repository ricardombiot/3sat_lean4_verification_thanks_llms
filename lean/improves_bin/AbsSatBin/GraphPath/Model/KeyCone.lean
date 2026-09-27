-- lean/improves_bin/AbsSatBin/GraphPath/Model/KeyCone.lean
import AbsSatBin.GraphPath.Model.M1Parts

/-!
# `KeyTri₁` split at the join (`docs/context/escalera_reader.md` §4.2ο.2)

`TriPin₁` climbs from a state below: if `P` sits below `K` (`Below K P`), `TriPin₁ P x` holds, and every
`x`-compatible link of `K` is already `x`-compatible in `P` (**`CxPull`**), then `TriPin₁ K x`
(**`triPin₁_of_below`**): the witnesses `P` gives are witnesses of `K`, with larger tables.

For the key `x` of a joined state pinned by `R`, `P` is the piece of `x.id` pinned by `R`. This separates the two
halves of `KeyTri₁`: `CxPull` is the mixing of the join (a compatible link of the union is a link of the key's
piece); `TriPin₁ P x` speaks of one piece only, where `x` sits in the top row of the source.
-/

namespace AbsSatBin.GraphPath.Model.KeyCone

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.TriPinCut

/-- Every `x`-compatible link of `K` between nodes that own `x` is `x`-compatible in `P`. -/
def CxPull (K P : GPathM) (x : PathNodeId) : Prop :=
  ∀ y ny w, K.node? y = some ny → x ∈ ny.owners → (∃ nw, K.node? w = some nw ∧ x ∈ nw.owners) → Cx K x ny w →
    ∃ nyP nwP, P.node? y = some nyP ∧ P.node? w = some nwP ∧ x ∈ nyP.owners ∧ x ∈ nwP.owners ∧ Cx P x nyP w

/-- `Cx` climbs to a state above. -/
theorem cx_up {K P : GPathM} (hb : Below K P) (x : PathNodeId) (ny : PNodeM) (nyK : PNodeM)
    (hoy : ∀ q ∈ ny.owners, q ∈ nyK.owners) (w : PathNodeId) (h : Cx P x ny w) : Cx K x nyK w := by
  obtain ⟨nw, nx, hw, hx, hwy, hl⟩ := h
  obtain ⟨nwK, hwK, how, _, _⟩ := hb.node w nw hw
  obtain ⟨nxK, hxK, hox, _, _⟩ := hb.node x nx hx
  refine ⟨nwK, nxK, hwK, hxK, hoy w hwy, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrw, hrx, hrs⟩ := hl l h0 (by rw [← hb.step]; exact h1)
  exact ⟨r, hoy r hr, how r hrw, hox r hrx, hrs⟩

/-- **`TriPin₁` climbs from a state below along pulled links.** -/
theorem triPin₁_of_below {K P : GPathM} (hb : Below K P) (x : PathNodeId) (ht : TriPin₁ P x)
    (hp : CxPull K P x) : TriPin₁ K x := by
  intro y ny w nw nx hy hw hx hxy hxw hC l h0 h1
  obtain ⟨nyP, nwP, hyP, hwP, hxyP, hxwP, hCP⟩ := hp y ny w hy hxy ⟨nw, hw, hxw⟩ hC
  obtain ⟨_, nxP, _, hxP, _, _⟩ := id hCP
  obtain ⟨nyK, hyK, hoy, _, _⟩ := hb.node y nyP hyP
  obtain ⟨nwK, hwK, how, _, _⟩ := hb.node w nwP hwP
  obtain ⟨nxK, hxK, hox, _, _⟩ := hb.node x nxP hxP
  rw [hy] at hyK; cases hyK
  rw [hw] at hwK; cases hwK
  rw [hx] at hxK; cases hxK
  obtain ⟨r, hr, hrw, hrx, hrs, hcy, hcw⟩ :=
    ht y nyP w nwP nxP hyP hwP hxP hxyP hxwP hCP l h0 (by rw [← hb.step]; exact h1)
  exact ⟨r, hoy r hr, how r hrw, hox r hrx, hrs, cx_up hb x nyP ny hoy r hcy, cx_up hb x nwP nw how r hcw⟩

variable (φ : Cnf) (hbd : Bounded φ)

/-- **`KeyTri₁` split at the join**: every live key of step `n` has a node `x` whose piece, pinned by the same pins,
is valid, satisfies `TriPin₁` at `x`, and receives every `x`-compatible link of the pinned joined state. -/
def KeySplit (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∀ q ∈ (filterAll kv'.2 ps).gowners, q.id.step = (n : Int) →
      ∃ x ∈ (filterAll kv'.2 ps).gowners, x.id = q.id ∧ ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧
        isValid (upF φ kv.2 kv'.1) = true ∧ isValid (filterAll (upF φ kv.2 kv'.1) ps) = true ∧
        TriPin₁ (filterAll (upF φ kv.2 kv'.1) ps) x ∧
        CxPull (filterAll kv'.2 ps) (filterAll (upF φ kv.2 kv'.1) ps) x

include hbd

/-- **`KeySplit ⇒ KeyTri₁`**: the pinned piece is a kernel below the pinned joined state (`below_filterAll`), and
`TriPin₁` climbs (`triPin₁_of_below`). -/
theorem keyTri₁_of_split (n : Nat) (hS : KeySplit φ n) : M1Parts.KeyTri₁ φ n := by
  intro kv' hkv' ps hv q hq hqn
  obtain ⟨x, hx, hxq, kv, hkv, hd, hvP0, hvP, ht, hp⟩ := hS kv' hkv' ps hv q hq hqn
  have hok := (lineOk φ n).2 kv hkv
  obtain ⟨h, hh, hg⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvP0
  have heq : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hh kv' hkv' rfl
  have hbJP : Below kv'.2 (upF φ kv.2 kv'.1) := by rw [← heq]; exact PieceFilter.below_of_grown hg
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvP0
  have cP := filt_ctx φ hbd _ _ hP ps hvP
  have hbP := PieceFilter.below_trans hbJP (KernelIff.below_filterAll_self _ (FExtInd.nodup_ok φ hbd _ _ hP) ps)
  have hbK : Below (filterAll kv'.2 ps) (filterAll (upF φ kv.2 kv'.1) ps) :=
    below_filterAll cP.pc.ker hbP ps (fun r hr z hz hzs => LineUnion.gowner_pinned _ ps z hz r hr hzs)
  exact ⟨x, hx, hxq, triPin₁_of_below hbK x ht hp⟩

/-- **The reader decides `φ` under `KeySplit` and `M1bLowOwn` at every join.** -/
theorem readerVerdictW_iff_of_split
    (hS : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → KeySplit φ n)
    (hO : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1Parts.M1bLowOwn φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  M1Parts.readerVerdictW_iff_of_keyTri₁ φ hbd (fun n h1 hn => keyTri₁_of_split φ hbd n (hS n h1 hn)) hO

end AbsSatBin.GraphPath.Model.KeyCone

/-- info: 'AbsSatBin.GraphPath.Model.KeyCone.triPin₁_of_below' does not depend on any axioms -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.KeyCone.triPin₁_of_below

/-- info: 'AbsSatBin.GraphPath.Model.KeyCone.readerVerdictW_iff_of_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.KeyCone.readerVerdictW_iff_of_split
