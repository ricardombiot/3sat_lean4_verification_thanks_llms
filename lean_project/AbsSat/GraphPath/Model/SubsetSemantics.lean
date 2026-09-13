-- lean_project/AbsSat/GraphPath/Model/SubsetSemantics.lean
import AbsSat.GraphPath.Model.UnitPropagation
import AbsSat.GraphPath.Model.Reader
import AbsSat.GraphPath.Model.Sons

/-!
# A state is a subset of partial paths, and the filter is an exact intersection

The author's framing: the machine does not reason about individual owner facts; each
state is a **subset of partially built paths**, and the operations are set operations.
In those terms the Helly gap does not appear inside the operations — a path either
goes through every pin or it does not.

* `denotS g p` — the subset a state holds: the paths of its sound chains.
* `denotS_filterAll` — for a reachable state whose filter is valid,
  `denotS (filterAll g reqs) = denotS g ∩ {paths through every pin}`, **exactly**.

`⊇` is `ChainSound_filterAll`: a sound chain through the pins survives the filter.
`⊆` carries a sound chain of the filtered state back across the narrowing
(`ChainSound_of_pruned`, with unique ids and the son/parent mirror of reachable
states), and `pinned_step_pure` puts it through the pins.

What stays open is not here: the machine tests a subset for emptiness by looking at
`isValid` on its compressed owner tables, not at the subset.
-/

namespace AbsSat.GraphPath.Model.SubsetSemantics

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.UnitPropagation

/-- The subset of partial paths a state holds: the paths of its sound chains. -/
def denotS (g : GPathM) (p : List NodeId) : Prop := ∃ sel, ChainSound g sel ∧ p = pathOf sel g

/-- Along a chain, a path goes through a node of its range exactly at that node's
step. -/
theorem mem_pathOf_iff (g : GPathM) (sel : Int → PathNodeId) (hchain : IsChain g sel)
    (r : NodeId) (h0 : 0 ≤ r.step) (hlt : r.step < g.current_step) :
    r ∈ pathOf sel g ↔ (sel r.step).id = r := by
  simp only [pathOf, List.mem_map, List.mem_reverse]
  constructor
  · rintro ⟨k, hk, hkr⟩
    have hk0 := mem_intRange_lower hk
    have hk1 := mem_intRange_upper hk
    have hstep := (hchain.1 k hk0 (by omega)).2
    rw [hkr] at hstep
    rw [hstep]
    exact hkr
  · intro h
    exact ⟨r.step, mem_intRange h0 (by omega), h⟩

/-- A sound chain after a narrowing was already a sound chain before it. -/
theorem ChainSound_of_pruned {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (hsmp : Sons.SMP g) (sel : Int → PathNodeId) (h : ChainSound g' sel) :
    ChainSound g sel := by
  obtain ⟨hchain', howned', hgow'⟩ := h.chain
  have hchain := IsChain_of_pruned hpr hnd sel hchain'
  refine ⟨⟨hchain, PairwiseOwned_of_pruned hpr hnd sel howned',
    fun k h0 hk => hpr.gowners_sub _ (hgow' k h0 (by rw [hpr.step_eq]; exact hk))⟩, ?_, ?_, ?_⟩
  · intro k h0 hk
    have hso := h.self_owned k h0 (by rw [hpr.step_eq]; exact hk)
    simp only [ownersOf] at hso ⊢
    cases hn' : g'.node? (sel k) with
    | none => rw [hn'] at hso; exact absurd hso List.not_mem_nil
    | some n' =>
      rw [hn'] at hso
      have hn'_mem : n' ∈ g'.nodes := List.mem_of_find?_eq_some hn'
      have hn'_id : n'.id = sel k := node?_id_eq g' (sel k) n' hn'
      obtain ⟨n, hn, hid, hsub, _⟩ := hpr.nodes_derived n' hn'_mem
      have hnid : n.id = sel k := by rw [← hid]; exact hn'_id
      rw [show g.node? (sel k) = some n by rw [← hnid]; exact node?_of_mem hnd n hn]
      exact hsub _ hso
  · exact Sons.son_link_of_SMP g hsmp sel hchain
  · have hrs := h.root_shape
    rw [hpr.step_eq] at hrs
    exact hrs

/-- `⊇`: a path of the subset that goes through every pin survives the filter. -/
theorem denotS_filterAll_of (g : GPathM) (reqs : List NodeId) (p : List NodeId)
    (hp : denotS g p)
    (hthrough : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → req ∈ p) :
    denotS (filterAll g reqs) p := by
  obtain ⟨sel, hsound, rfl⟩ := hp
  obtain ⟨hchain, _, _⟩ := hsound.chain
  refine ⟨sel, ChainSound_filterAll g reqs sel hsound
    (fun req hreq h0 hlt => (mem_pathOf_iff g sel hchain req h0 hlt).mp (hthrough req hreq h0 hlt)), ?_⟩
  simp only [pathOf, (pruned_filterAll g reqs).step_eq]

/-- **The filter is an exact intersection of subsets.** For a reachable state whose
filter is valid, the subset after `filterAll` is the subset before it, intersected
with the paths that go through every pin. -/
theorem denotS_filterAll (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) (p : List NodeId) :
    denotS (filterAll g reqs) p ↔
      denotS g p ∧ ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → req ∈ p := by
  constructor
  · rintro ⟨sel, hsound, rfl⟩
    have hpr := pruned_filterAll g reqs
    have hsg := ChainSound_of_pruned hpr (Reader.NodupIds_reachable reqOf g hr)
      (Sons.SMP_reachable reqOf g hr) sel hsound
    obtain ⟨hchain, _, _⟩ := hsg.chain
    obtain ⟨hchain', _, _⟩ := hsound.chain
    have hpath : pathOf sel (filterAll g reqs) = pathOf sel g := by
      simp only [pathOf, hpr.step_eq]
    refine ⟨⟨sel, hsg, hpath⟩, fun req hreq h0 hlt => ?_⟩
    rw [hpath]
    refine (mem_pathOf_iff g sel hchain req h0 hlt).mpr ?_
    obtain ⟨hsome, hstep⟩ := hchain'.1 req.step h0 (by rw [hpr.step_eq]; exact hlt)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    have hnmem : n ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hn
    have hnid : n.id = sel req.step := node?_id_eq _ _ n hn
    have hpure := pinned_step_pure g (SelfOwn.OOS_reachable reqOf g hr) reqs hv req hreq hlt h0
      n hnmem (by rw [hnid, hstep])
    rw [hnid] at hpure
    exact hpure
  · rintro ⟨hp, hthrough⟩
    exact denotS_filterAll_of g reqs p hp hthrough

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.ChainSound_of_pruned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_of_pruned

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.denotS_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denotS_filterAll

end AbsSat.GraphPath.Model.SubsetSemantics
