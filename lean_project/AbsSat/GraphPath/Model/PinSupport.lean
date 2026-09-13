-- lean_project/AbsSat/GraphPath/Model/PinSupport.lean
import AbsSat.GraphPath.Model.UnitPropagation

/-!
# A value survives a filter only with the pins in its owners table

Classified on `SatMachinePure` (seed 31337, the eight values the review removes
while unit propagation still allows them): every one dies in the first
`cleanInvalid`, because at a pinned step its owners carry only values the pin
removed. Unit propagation cannot see it — it keeps one domain per variable — but the
owners table records which values live together inside the state, including at a
distance (a node at step 10 whose only owner at step 7 was the pinned-out value).

* `pinned_support` — if the filtered state is valid and a map node survives, some
  node carrying it already owned, at every pinned step, a node with exactly the
  pinned id.
* `removed_unless_supported` — the usable direction: if no node carrying the value
  owns every pin, the filter either invalidates the state or removes the value.

Only `GN` (global owners are nodes) is needed, which every reachable state has.
-/

namespace AbsSat.GraphPath.Model.PinSupport

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.LocalContradiction
open AbsSat.GraphPath.Model.UnitPropagation

/-- **What survives a filter owned the pins.** -/
theorem pinned_support (g : GPathM) (hgn : GownersNodes.GN g) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) (r : NodeId)
    (hp : Present (filterAll g reqs) r) :
    ∃ n ∈ g.nodes, n.id.id = r ∧
      ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → ∃ q ∈ n.owners, q.id = req := by
  obtain ⟨o, ho, hoid⟩ := hp
  obtain ⟨d, hd, hdid, hvalid, hfix⟩ :=
    node_of_gowner g reqs hv (GownersNodes.GN_filterAll g reqs hgn) o ho
  obtain ⟨n, hn, hid, hown, _⟩ := (pruned_filterAll g reqs).nodes_derived d hd
  refine ⟨n, hn, by rw [← hid, hdid]; exact hoid, ?_⟩
  intro req hreq h0 hlt
  obtain ⟨q, hq, hqs, hqg⟩ := owner_at_step g reqs hv d hvalid hfix req.step h0 hlt
  have hq0 := (pruned_review (reqs.foldl filterRequire g)).gowners_sub q hqg
  rcases (mem_foldl_filterRequire reqs g q hq0).2 req hreq with h | h
  · exact absurd hqs h
  · exact ⟨q, hown q hq, h⟩

/-- **A value that never lives with the pins is removed.** If every node carrying
`r` lacks, at some pinned step, an owner with the pinned id, then the filter either
leaves the state invalid or removes `r`. -/
theorem removed_unless_supported (g : GPathM) (hgn : GownersNodes.GN g) (reqs : List NodeId)
    (r : NodeId)
    (hns : ∀ n ∈ g.nodes, n.id.id = r →
      ∃ req ∈ reqs, 0 ≤ req.step ∧ req.step < g.current_step ∧ ∀ q ∈ n.owners, q.id ≠ req) :
    isValid (filterAll g reqs) = false ∨ ¬ Present (filterAll g reqs) r := by
  cases hv : isValid (filterAll g reqs) with
  | false => exact Or.inl rfl
  | true =>
    refine Or.inr fun hp => ?_
    obtain ⟨n, hn, hid, hsupp⟩ := pinned_support g hgn reqs hv r hp
    obtain ⟨req, hreq, h0, hlt, hnone⟩ := hns n hn hid
    obtain ⟨q, hq, hqr⟩ := hsupp req hreq h0 hlt
    exact hnone q hq hqr

/-- info: 'AbsSat.GraphPath.Model.PinSupport.pinned_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinned_support

/-- info: 'AbsSat.GraphPath.Model.PinSupport.removed_unless_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms removed_unless_supported

end AbsSat.GraphPath.Model.PinSupport
