-- lean_project/AbsSat/GraphPath/Model/PinExactBoundary.lean
import AbsSat.GraphPath.Model.PinExact
import AbsSat.GraphPath.Model.AggFixpoint

/-!
# Symmetry of owners on every reader state

`PinExact.sat_of_pinExact` asks for symmetric owner tables at every state the reader visits. Since the
author's 14-sept change the aggressive sweep visits every step and drops asymmetric entries, so
`AggFixpoint.AggOk` gives symmetry directly (report v121). (Before, only the interior steps were
covered, and the rest was the open obligation `BoundarySym`, now gone.)

* `ownSymmetric_of_aggOk` — `AggOk`, node steps in range and valid nodes give full symmetry.
* `readFrom_form` — every state the reader visits is a result of the aggressive review.
* **`sat_of_pinExactAgg`** — the soundness of the Improves verdict from `PinExact` alone along the
  reader's states.
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

/-- **Owner tables are symmetric** at a state passing the author's tests. -/
theorem ownSymmetric_of_aggOk (g : GPathM) (hok : AggOk g) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hval : ∀ pid n, g.node? pid = some n → isValidNode g n = true) :
    Threaded.OwnSymmetric g := by
  intro p n q m hn hm hq
  have hnm := List.mem_of_find?_eq_some hn
  have hmm := List.mem_of_find?_eq_some hm
  have hpid := node?_id_eq g p n hn
  have hqid := node?_id_eq g q m hm
  exact ownSym_of_aggOk g hok p q n m hn hm (by rw [← hpid]; exact hsnn n hnm)
    (by rw [← hpid]; exact hbelow n hnm) (by rw [← hqid]; exact hsnn m hmm)
    (by rw [← hqid]; exact hbelow m hmm) hq (hval p n hn) (hval q m hm)

/-- Every state the reader visits from a reviewed state is a result of the aggressive review. -/
theorem readFrom_form (g₀ : GPathM) (h₀ : ∃ y reqs, g₀ = filterAllAgg y reqs) :
    ∀ g, ReadFrom g₀ g → ∃ y reqs, g = filterAllAgg y reqs := by
  intro g hF
  induction hF with
  | start => exact h₀
  | pin g' mid _ _ _ => exact ⟨g', [mid], rfl⟩

/-- **Soundness of the Improves verdict from `PinExact` along the reader's states.** -/
theorem sat_of_pinExactAgg (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hpe : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true →
      ∀ p ∈ g.gowners, PinExact g p.id) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  refine sat_of_pinExact φ hwf kv hkv hv (fun g hF hvg => ?_) hpe
  have hR : ReadableAgg g := readableAgg_of_readFrom _ ⟨kv.2, [], hm.rctx, rfl⟩ g hF
  obtain ⟨y, reqs, rfl⟩ := readFrom_form _ ⟨kv.2, [], rfl⟩ g hF
  have ctx := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hR) hvg
  have rc := RCtx_of_readableAgg _ hR
  exact ownSymmetric_of_aggOk _ (aggOk_reviewAgg _ hvg) rc.snn rc.below ctx.nodeval

/-- info: 'AbsSat.GraphPath.Model.PinExactBoundary.sat_of_pinExactAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinExactAgg

end AbsSat.GraphPath.Model.PinExactBoundary
