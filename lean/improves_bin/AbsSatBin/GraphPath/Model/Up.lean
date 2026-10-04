-- lean/improves_bin/AbsSatBin/GraphPath/Model/Up.lean
import AbsSatBin.GraphPath.Model.Join

/-!
Bridge lemma **L3** (`formal_bridge_owners_runpure.md` §5): UP respects the
denotation.

    denot (up_filtering g (requires d) d)
      = { d.id :: p | p ∈ denot g, p satisfies requires d }

**What is proved here: the ⊆ direction.** `denot_upFiltering` and
`denot_upFiltering_base` — every path the extended graph denotes is `d`
followed by a path the base graph denotes.

The argument is the structural one: `up` adds exactly *one* node, so the top
line holds exactly one node and every chain is forced to select it there
(`chain_top_is_new`); below that step the extended graph has precisely `g`'s
nodes, with parents untouched and owners grown by the single new id
(`addNode_node?_below`), so the rest of the chain restricts to a chain of `g`.
`pathOf` is built over the reversed step range, which is why the new node ends
up at the *head* of the path.

The "satisfies `requires d`" half of the ⊆ direction is
`Filter.chain_selects_req`: in a valid filtered graph every chain selects the
required node at its step. The two together are L3's soundness content.

**What is not proved: the ⊇ direction** — a chain of `g` that satisfies the
requirements survives the filter and extends to a chain of the result. It
needs two things this module does not have: that filtering keeps the chain
alive, which is lemma **L6**; and that every chain node is a global owner, so
that the new node (whose owners are exactly `gowners`) co-owns it.

`chain_top_is_new` and `addNode_node?_below` both take `hbelow` — every node
of the base graph sits strictly below `current_step`. That is
`OwnersInvariants.steps_below_current`, discharged from `Reachable`.
-/

namespace AbsSatBin.GraphPath.Model
open AbsSatBin.Utils.Alias
open GPathM

/-!
The definitions `newParents`, `newRowIds`, `rowParents`, `rowOwners`, `rowNode`,
`newRow`, `gainedSons`, `gainedOwners`, `upSons`, `upOwners` and `upMap` live in
`GPathM.lean`, next to `addNode` itself. What follows are their shape lemmas.
-/


/-- An identifier the **shift** does not produce has no parents there.

**Bin map: the hypothesis changed.** `lean_project` had `p ∉ newRowIds g d`. With prohibited
windows that is too weak: a prohibited identifier is not in the row, yet it *has* parents — the
nodes of the last row that shift onto it. The right hypothesis is that `p` is not a candidate. -/
theorem rowParents_of_not_mem (g : GPathM) (d : NodeId) (p : PathNodeId)
    (hpos : 0 < g.current_step) (h : p ∉ shiftRowIds g d) : rowParents g d p = [] := by
  rcases hr : rowParents g d p with _ | ⟨r, rest⟩
  · rfl
  · exfalso
    have hmem : r ∈ rowParents g d p := by rw [hr]; exact List.mem_cons_self
    have := shiftPid_of_mem_rowParents g d p r hmem
    apply h
    rw [← this]
    unfold shiftRowIds
    rw [if_pos hpos]
    exact (mem_dedupPids _ _).mpr (List.mem_map_of_mem (rowParents_subset g d p r hmem))

/-- And so it owns only itself: `rowOwners` collapses to the singleton. -/
theorem rowOwners_of_not_mem (g : GPathM) (d : NodeId) (p : PathNodeId)
    (hpos : 0 < g.current_step) (h : p ∉ shiftRowIds g d) : rowOwners g d p = [p] := by
  unfold rowOwners
  rw [rowParents_of_not_mem g d p hpos h]
  rfl

/-- Every row node has a parent (above step 0). -/
theorem exists_rowParent (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool)
    (hpos : 0 < g.current_step)
    {z : PathNodeId} (hz : z ∈ newRowIds g d forb) : ∃ r, r ∈ rowParents g d z := by
  obtain ⟨r, hr, hrz⟩ := exists_shift_of_mem_newRowIds g d forb z hpos hz
  exact ⟨r, List.mem_filter.mpr ⟨hr, beq_iff_eq.mpr hrz.symm⟩⟩

/-- A parent of a row node is a node of the state, at the top old step. -/
theorem rowParent_node (g : GPathM) (d : NodeId) (hpos : 0 < g.current_step)
    {z r : PathNodeId} (hr : r ∈ rowParents g d z) :
    (g.node? r).isSome = true ∧ r.id.step = g.current_step - 1 := by
  have hmem : r ∈ newParents g := rowParents_subset g d z r hr
  unfold newParents at hmem
  rw [if_pos hpos] at hmem
  obtain ⟨nr, hnr, hnrid⟩ := List.mem_map.mp hmem
  have hnmem : nr ∈ g.nodes := (List.mem_filter.mp hnr).1
  refine ⟨?_, ?_⟩
  · have := node?_isSome_of_mem g nr hnmem; rwa [hnrid] at this
  · rw [← hnrid]; exact eq_of_beq (List.mem_filter.mp hnr).2

-- ============================================================
-- `node?` through addNode
-- ============================================================

theorem addNode_node?_old (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (pid' : PathNodeId) (n : PNodeM) (hn : g.node? pid' = some n) :
    (addNode g d title forb).node? pid' = some (upMap g d forb n) := by
  have hp : (fun x : PNodeM => (upMap g d forb x).id == pid') = (fun x : PNodeM => x.id == pid') := by
    funext x; rw [upMap_id]
  simp only [node?, addNode_nodes, List.find?_append, List.find?_map, Function.comp_def, hp]
  rw [show g.nodes.find? (fun x : PNodeM => x.id == pid') = some n from hn]
  rfl

/-- Below the new step, the extended graph has exactly `g`'s nodes. -/
theorem addNode_node?_below (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (pid' : PathNodeId) (n' : PNodeM)
    (hn' : (addNode g d title forb).node? pid' = some n')
    (hstep : pid'.id.step < g.current_step) :
    ∃ n, g.node? pid' = some n ∧ n' = upMap g d forb n := by
  have hmem : n' ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hn'
  have hid : n'.id = pid' := node?_id_eq _ pid' n' hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hnid : n.id = pid' := by rw [← hid, ← hEq, upMap_id]
    have hsome : (g.node? n.id).isSome := node?_isSome_of_mem g n hn
    rw [hnid] at hsome
    obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨n₀, hn₀, ?_⟩
    have := addNode_node?_old g d title forb pid' n₀ hn₀
    rw [hn'] at this
    exact (Option.some.inj this)
  · exfalso
    have := newRow_step g d title forb hd n' hr
    rw [hid] at this
    omega

-- ============================================================
-- Restricting a chain of the extended graph
-- ============================================================

theorem IsChain_of_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (sel : Int → PathNodeId)
    (h : IsChain (addNode g d title forb) sel) : IsChain g sel := by
  constructor
  · intro k hlo hhi
    obtain ⟨hsome, hstep⟩ := h.1 k hlo (by rw [addNode_current]; omega)
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨n, hn, _⟩ := addNode_node?_below g d title forb hd _ n' hn' (by rw [hstep]; exact hhi)
    exact ⟨by rw [hn]; rfl, hstep⟩
  · intro k hlo hhi
    have hstep := (h.1 (k + 1) (by omega) (by rw [addNode_current]; omega)).2
    have hlink := h.2 k hlo (by rw [addNode_current]; omega)
    cases hn' : (addNode g d title forb).node? (sel (k + 1)) with
    | none => rw [hn'] at hlink; exact absurd hlink List.not_mem_nil
    | some n' =>
      obtain ⟨n, hn, hEq⟩ :=
        addNode_node?_below g d title forb hd _ n' hn' (by rw [hstep]; omega)
      rw [hn'] at hlink
      rw [hn]
      simpa [hEq, upMap_parents] using hlink

theorem PairwiseOwned_of_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (sel : Int → PathNodeId)
    (hchain : IsChain (addNode g d title forb) sel)
    (h : PairwiseOwned (addNode g d title forb) sel) : PairwiseOwned g sel := by
  intro i j hi hj hi' hj' hne
  have hmem := h i j hi hj (by rw [addNode_current]; omega) (by rw [addNode_current]; omega) hne
  have hstepi := (hchain.1 i hi (by rw [addNode_current]; omega)).2
  have hstepj := (hchain.1 j hj (by rw [addNode_current]; omega)).2
  simp only [ownersAt, List.mem_filter] at hmem ⊢
  obtain ⟨hown, hstep⟩ := hmem
  refine ⟨?_, hstep⟩
  simp only [ownersOf] at hown ⊢
  cases hn' : (addNode g d title forb).node? (sel j) with
  | none => rw [hn'] at hown; exact absurd hown List.not_mem_nil
  | some n' =>
    obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title forb hd _ n' hn' (by rw [hstepj]; exact hj')
    rw [hn'] at hown
    rw [hn]
    dsimp only at hown ⊢
    rw [hEq, upMap_owners] at hown
    rcases List.mem_append.mp hown with hl | hr
    · exact hl
    · exfalso
      have hmemids : sel i ∈ newRowIds g d forb := (List.mem_filter.mp hr).1
      have := mapId_of_mem_newRowIds g d forb _ hmemids
      rw [this] at hstepi
      rw [hd] at hstepi
      omega

-- ============================================================
-- The new node is what every chain selects at the top step
-- ============================================================

/-- **The chain picks a node of the new row at the top step.** With a window of
two the row is a single node and this pins the pick outright; with three the row
is a node per grandparent, so what is pinned is the *map id*, and which node of
the row is pinned by the pick below it (`ParentId.parentId_coherent`) and the one
below that (`ParentId.gparentId_coherent`). -/
theorem chain_top_mem_newRowIds (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hpos : 0 ≤ g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (sel : Int → PathNodeId) (h : IsChain (addNode g d title forb) sel) :
    sel g.current_step ∈ newRowIds g d forb := by
  obtain ⟨hsome, hstep⟩ := h.1 g.current_step hpos (by rw [addNode_current]; omega)
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
  have hid : n'.id = sel g.current_step := node?_id_eq _ _ n' hn'
  have hmem : n' ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · exfalso
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hlt := hbelow n hn
    have hnn : n'.id = n.id := by rw [← hEq, upMap_id]
    rw [← hnn, hid] at hlt
    omega
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb n').mp hr
    rw [← hid, rowNode_id]
    exact hpid

/-- **And so the top pick carries the map id the `UP` visited.** -/
theorem chain_top_mapId (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hpos : 0 ≤ g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (sel : Int → PathNodeId) (h : IsChain (addNode g d title forb) sel) :
    (sel g.current_step).id = d :=
  mapId_of_mem_newRowIds g d forb _ (chain_top_mem_newRowIds g d title forb hpos hbelow sel h)

-- ============================================================
-- The path splits at the new step
-- ============================================================

theorem intRange_zero_succ (n : Int) (h : 0 ≤ n) :
    intRange 0 n = intRange 0 (n - 1) ++ [n] := by
  simp only [intRange]
  have h1 : (n - 0 + 1).toNat = (n - 1 - 0 + 1).toNat + 1 := by omega
  rw [h1, List.range_succ, List.map_append]
  congr 1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Int.ofNat_eq_natCast]
  omega

theorem pathOf_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hpos : 0 ≤ g.current_step) (sel : Int → PathNodeId) :
    pathOf sel (addNode g d title forb) = (sel g.current_step).id :: pathOf sel g := by
  simp only [pathOf, addNode_current]
  rw [show g.current_step + 1 - 1 = g.current_step from by omega,
      intRange_zero_succ g.current_step hpos]
  simp

-- ============================================================
-- L3, soundness direction
-- ============================================================

/-- **L3 ⊆, for the `addNode` half of UP.** Every path the extended graph
denotes is `d` followed by a path the base graph denotes: every node of the top
row carries the map id `d`, so every chain reports `d` there, and the rest of
the chain is a chain of the base graph. -/
theorem denot_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hpos : 0 ≤ g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (p : List NodeId) (h : denot (addNode g d title forb) p) :
    ∃ p', p = d :: p' ∧ denot g p' := by
  obtain ⟨sel, hchain, howned, hpath⟩ := h
  refine ⟨pathOf sel g, ?_, sel, IsChain_of_addNode g d title forb hd sel hchain,
    PairwiseOwned_of_addNode g d title forb hd sel hchain howned, rfl⟩
  rw [hpath, pathOf_addNode g d title forb hpos sel,
      chain_top_mapId g d title forb hpos hbelow sel hchain]

/-- **L3 ⊆, as the machine calls it.** In the bin map the UP reviews after skipping a window;
the review only narrows (`denot_review_subset`), which needs the row's ids to be distinct
(`hndUp`, from `Reader.nodupIds_addNode`). -/
theorem denot_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool)
    (hvalid : isValid (filterAll g reqs) = true)
    (hpos : 0 ≤ g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes, n.id.id.step < (filterAll g reqs).current_step)
    (hndUp : NodupIds (addNode (filterAll g reqs) d title forb))
    (p : List NodeId) (h : denot (upFiltering g reqs d title forb) p) :
    ∃ p', p = d :: p' ∧ denot (filterAll g reqs) p' := by
  have hstep : (filterAll g reqs).current_step = g.current_step :=
    (pruned_filterAll g reqs).step_eq
  have hadd : denot (addNode (filterAll g reqs) d title forb) p := by
    simp only [upFiltering, up, hvalid, if_true] at h
    split at h
    · exact denot_review_subset _ hndUp p h
    · exact h
  exact denot_addNode _ d title forb (by omega) (by omega) hbelow p hadd

/-- **L3 ⊆, all the way back to the unfiltered graph.** Needs `NodupIds` for
the same reason `denot_filterAll_subset` does: `node?` takes the first match,
so pruning can shadow a node if ids repeat. -/
theorem denot_upFiltering_base (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool)
    (hvalid : isValid (filterAll g reqs) = true)
    (hpos : 0 ≤ g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes, n.id.id.step < (filterAll g reqs).current_step)
    (hnd : NodupIds g) (hndUp : NodupIds (addNode (filterAll g reqs) d title forb))
    (p : List NodeId) (h : denot (upFiltering g reqs d title forb) p) :
    ∃ p', p = d :: p' ∧ denot g p' := by
  obtain ⟨p', hp, hden⟩ := denot_upFiltering g reqs d title forb hvalid hpos hd hbelow hndUp p h
  exact ⟨p', hp, denot_filterAll_subset g hnd reqs p' hden⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSatBin.GraphPath.Model.denot_upFiltering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_upFiltering

/-- info: 'AbsSatBin.GraphPath.Model.denot_upFiltering_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_upFiltering_base

end AbsSatBin.GraphPath.Model
