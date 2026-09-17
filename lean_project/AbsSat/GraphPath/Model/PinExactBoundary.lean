-- lean_project/AbsSat/GraphPath/Model/PinExactBoundary.lean
import AbsSat.GraphPath.Model.PinExact
import AbsSat.GraphPath.Model.AggFixpoint

/-!
# Symmetry of owners: only the two extreme steps are left

`PinExact.sat_of_pinExact` asks for symmetric owner tables at every state the reader visits.
`AggFixpoint.ownSym_of_aggOk` proves symmetry for every valid result of the aggressive review, on the
steps its sweep visits (`1 … current_step − 2`). Every state the reader visits is such a result, so
only pairs touching step `0` or step `current_step − 1` remain.

* `BoundarySym g` — symmetry for owner pairs with one end on an extreme step.
* `ownSymmetric_of_boundary` — `AggOk`, `OOS`, valid nodes and `BoundarySym` give full symmetry.
* **`sat_of_pinExact_boundary`** — the soundness of the Improves verdict from `PinExact` and
  `BoundarySym` along the reader's states.
-/

namespace AbsSat.GraphPath.Model.PinExactBoundary

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.AggFixpoint
open AbsSat.GraphPath.Model.PinExact

/-- Symmetry for owner pairs with one end on step `0` or on the top step. -/
def BoundarySym (g : GPathM) : Prop :=
  ∀ p n q m, g.node? p = some n → g.node? q = some m → q ∈ n.owners →
    ¬ (1 ≤ p.id.step ∧ p.id.step ≤ g.current_step - 2 ∧ 1 ≤ q.id.step ∧ q.id.step ≤ g.current_step - 2) →
    p ∈ m.owners

theorem ownSymmetric_of_boundary (g : GPathM) (hok : AggOk g) (hoos : SelfOwn.OOS g)
    (hval : ∀ pid n, g.node? pid = some n → isValidNode g n = true) (hb : BoundarySym g) :
    Threaded.OwnSymmetric g := by
  intro p n q m hn hm hq
  by_cases hin : 1 ≤ p.id.step ∧ p.id.step ≤ g.current_step - 2 ∧ 1 ≤ q.id.step ∧
      q.id.step ≤ g.current_step - 2
  · exact ownSym_of_aggOk g hok hoos p q n m hn hm hin.1 hin.2.1 hin.2.2.1 hin.2.2.2 hq
      (hval p n hn) (hval q m hm)
  · exact hb p n q m hn hm hq hin

/-- Every state the reader visits from a reviewed state is a result of the aggressive review. -/
theorem readFrom_form (g₀ : GPathM) (h₀ : ∃ y reqs, g₀ = filterAllAgg y reqs) :
    ∀ g, ReadFrom g₀ g → ∃ y reqs, g = filterAllAgg y reqs := by
  intro g hF
  induction hF with
  | start => exact h₀
  | pin g' mid _ _ _ => exact ⟨g', [mid], rfl⟩

/-- **Soundness of the Improves verdict from `PinExact` and symmetry on the extreme steps.** -/
theorem sat_of_pinExact_boundary (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hb : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → BoundarySym g)
    (hpe : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true →
      ∀ p ∈ g.gowners, PinExact g p.id) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  refine sat_of_pinExact φ hwf kv hkv hv (fun g hF hvg => ?_) hpe
  have hR : ReadableAgg g := readableAgg_of_readFrom _ ⟨kv.2, [], hm.rctx, rfl⟩ g hF
  obtain ⟨y, reqs, rfl⟩ := readFrom_form _ ⟨kv.2, [], rfl⟩ g hF
  have ctx := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hR) hvg
  exact ownSymmetric_of_boundary _ (aggOk_reviewAgg _ hvg) (RCtx_of_readableAgg _ hR).oos
    ctx.nodeval (hb _ hF hvg)

/-- info: 'AbsSat.GraphPath.Model.PinExactBoundary.sat_of_pinExact_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinExact_boundary

end AbsSat.GraphPath.Model.PinExactBoundary
