-- lean_project/AbsSat/GraphPath/Model/PinExactSome.lean
import AbsSat.GraphPath.Model.SliceExact

/-!
# The reader needs one exact pin per state, not all of them

`PinExact.sat_of_pinExact` and `PinExactBoundary.sat_of_pinExactAgg` ask for `PinExact` at **every**
pin of every state the reader visits. The reading loop only needs **one** valid pin at a step with a
choice, so this module asks for one exact pin per state. (With the sweep before the author's
14-sept change, `helly depth2` found reader states two pins deep where a pin on step `0` is valid but
does not keep its slice; report v121.)

* `pickSomeAgg_of_somePinExact` — with symmetric owners, one exact pin at a step with a choice gives
  `PickSomeAgg`.
* **`sat_of_somePinExact`** — the soundness of the Improves verdict when every state the reader visits
  that still has a choice has, at some step with a choice, a global owner whose pin is exact.
* **`sat_of_someSupported`** — the same with a supported slice (`SliceSupport.Supported`), a static
  condition on the state before the pin.
-/

namespace AbsSat.GraphPath.Model.PinExactSome

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PinExact
open AbsSat.GraphPath.Model.PinExactBoundary
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)

/-- **One exact pin at a step with a choice gives `PickSomeAgg`.** -/
theorem pickSomeAgg_of_somePinExact (g : GPathM) (ctx : Pinned.Ctx g) (hnd : NodupIds g)
    (hsym : Threaded.OwnSymmetric g)
    (h : hasChoice g = true → ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
      ∃ q ∈ ownersAt g.gowners k, PinExact g q.id) :
    PickSomeAgg g := by
  intro hch
  obtain ⟨k, hk0, hk1, hck, q, hq, hpe⟩ := h hch
  exact ⟨k, hk0, hk1, hck, q, hq,
    isValid_pin_of_pinExact g ctx hnd hsym q (List.mem_filter.mp hq).1 hpe⟩

/-- **Soundness of the Improves verdict from one exact pin per reader state.** -/
theorem sat_of_somePinExact (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hpe : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → hasChoice g = true →
      ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
        ∃ q ∈ ownersAt g.gowners k, PinExact g q.id) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  refine ReaderAggRun.sat_of_pickSomeAgg φ hwf kv hkv hv (fun g hF hvg => ?_)
  have hR : ReadableAgg g := readableAgg_of_readFrom _ ⟨kv.2, [], hm.rctx, rfl⟩ g hF
  obtain ⟨y, reqs, hy⟩ := readFrom_form _ ⟨kv.2, [], rfl⟩ g hF
  have ctx := Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hvg
  have hok : AggFixpoint.AggOk g := by
    rw [hy] at hvg ⊢
    exact AggFixpoint.aggOk_reviewAgg _ hvg
  have hsym := ownSymmetric_of_aggOk g hok (RCtx_of_readableAgg g hR).snn (RCtx_of_readableAgg g hR).below
    ctx.nodeval
  exact pickSomeAgg_of_somePinExact g ctx (RCtx_of_readableAgg g hR).nodup hsym (hpe g hF hvg)

/-- **The same with a supported slice**, a condition on the state before the pin. -/
theorem sat_of_someSupported (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hsup : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → hasChoice g = true →
      ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
        ∃ q ∈ ownersAt g.gowners k, SliceSupport.Supported g q.id) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have hs₀ : Sons.SMP (filterAllAgg kv.2 []) :=
    AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
  refine sat_of_somePinExact φ hwf kv hkv hv (fun g hF hvg hch => ?_)
  obtain ⟨k, hk0, hk1, hck, q, hq, hs⟩ := hsup g hF hvg hch
  have hR : ReadableAgg g := readableAgg_of_readFrom _ hR₀ g hF
  have rc := RCtx_of_readableAgg g hR
  exact ⟨k, hk0, hk1, hck, q, hq,
    SliceSupport.pinExact_of_supported g (Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hvg)
      rc.nodup rc.oos rc.snn rc.below (SliceSupport.smp_readFrom _ hR₀ hs₀ g hF) rc.shape.notroot q.id hs⟩

/-- info: 'AbsSat.GraphPath.Model.PinExactSome.sat_of_someSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_someSupported


end AbsSat.GraphPath.Model.PinExactSome
