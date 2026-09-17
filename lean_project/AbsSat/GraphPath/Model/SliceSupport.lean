-- lean_project/AbsSat/GraphPath/Model/SliceSupport.lean
import AbsSat.GraphPath.Model.PinExactBoundary
import AbsSat.GraphPath.Model.AnchoredSurvive

/-!
# `PinExact` from a support relation on the slice

`AnchoredSurvive.gowners_filterAllAgg_of_AOk` proves that a set held up by a support relation `R`
survives a compatible pin and the whole aggressive review. This module applies it to the slice of a
map node `mid`.

* `Slice g mid` — global owners whose node has an owner carrying `mid`.
* `Supported g mid` — some `R` holds the slice up (`Sup g (Slice g mid) R`).
* `slice_pinned` — the slice is compatible with the pin: by `OOS`, a member on the pinned step is its
  own owner there, so it carries `mid`.
* **`pinExact_of_supported`** — `Supported` gives `PinExact`.
* `smp_readFrom` — every state the reader visits keeps `Sons.SMP` (`MInv.smp` at the start, and the
  aggressive review keeps it).
* **`sat_of_supported_boundary`** — the soundness of the Improves verdict from `Supported` and
  `BoundarySym` along the reader's states.

The probe `helly gfp` / `helly gfpE` (report v119) measured that the largest relation meeting the
`Sup` conditions inside the slice's owner entries coincides with the owner tables the cascade leaves:
`Supported` is what the machine computes, stated on the state before the pin. Whether that largest
relation always covers the slice is the open part.
-/

namespace AbsSat.GraphPath.Model.SliceSupport

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PinExact
open AbsSat.GraphPath.Model.PinExactBoundary
open AbsSat.GraphPath.Model.AnchoredSurvive

/-- The slice of `mid`: global owners whose node has an owner carrying `mid`. -/
def Slice (g : GPathM) (mid : NodeId) (p : PathNodeId) : Prop :=
  p ∈ g.gowners ∧ ∃ n, g.node? p = some n ∧ InSlice n mid

/-- **The slice of `mid` is held up by a support relation.** -/
def Supported (g : GPathM) (mid : NodeId) : Prop :=
  ∃ R : PathNodeId → PathNodeId → Prop, Sup g (Slice g mid) R

/-- The slice is compatible with pinning `mid`. -/
theorem slice_pinned (g : GPathM) (hoos : SelfOwn.OOS g) (mid : NodeId) :
    ∀ p, Slice g mid p → p.id.step = mid.step → p.id = mid := by
  rintro p ⟨_, n, hn, q, hq, hqid⟩ hstep
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = p := node?_id_eq g p n hn
  have hqp : q = n.id := hoos n hmem q hq (by rw [hqid, hid, hstep])
  rw [← hid, ← hqp, hqid]

/-- **A supported slice survives its pin: `PinExact`.** -/
theorem pinExact_of_supported (g : GPathM) (ctx : Pinned.Ctx g) (hnd : NodupIds g)
    (hoos : SelfOwn.OOS g) (hsnn : SelfOwn.SNN g) (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hsmp : Sons.SMP g) (hnr : Parents.NotRoot g) (mid : NodeId) (hs : Supported g mid) :
    PinExact g mid := by
  intro n hn hin
  obtain ⟨R, hR⟩ := hs
  have hnd' : g.node? n.id = some n := node?_of_mem hnd n hn
  have hgow : n.id ∈ g.gowners :=
    (List.mem_filter.mp (Pinned.mem_ownersAt_gowners g ctx n.id n hnd' (hsnn n hn) (hbelow n hn))).1
  refine gowners_filterAllAgg_of_AOk g ⟨hR, hsmp, hnr⟩ [mid] ?_ n.id ⟨hgow, n, hnd', hin⟩
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact slice_pinned g hoos mid

/-- Every state the reader visits keeps `SMP`. -/
theorem smp_readFrom (g₀ : GPathM) (hR₀ : ReadableAgg g₀) (hs₀ : Sons.SMP g₀) :
    ∀ g, ReadFrom g₀ g → Sons.SMP g := by
  intro g hF
  induction hF with
  | start => exact hs₀
  | pin g' mid hF' _ ih =>
    exact SMP_filterAllAgg g' ih
      (RCtx_of_readableAgg g' (readableAgg_of_readFrom g₀ hR₀ g' hF')).shape.notroot [mid]

/-- **Soundness of the Improves verdict from a supported slice at every pin, and symmetry on the
extreme steps, along the reader's states.** -/
theorem sat_of_supported_boundary (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hb : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → BoundarySym g)
    (hsup : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true →
      ∀ p ∈ g.gowners, Supported g p.id) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have hs₀ : Sons.SMP (filterAllAgg kv.2 []) :=
    SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
  refine sat_of_pinExact_boundary φ hwf kv hkv hv hb (fun g hF hvg p hp => ?_)
  have hR : ReadableAgg g := readableAgg_of_readFrom _ hR₀ g hF
  have rc := RCtx_of_readableAgg g hR
  exact pinExact_of_supported g (Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hvg)
    rc.nodup rc.oos rc.snn rc.below (smp_readFrom _ hR₀ hs₀ g hF) rc.shape.notroot p.id
    (hsup g hF hvg p hp)

/-- info: 'AbsSat.GraphPath.Model.SliceSupport.sat_of_supported_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_supported_boundary

end AbsSat.GraphPath.Model.SliceSupport
