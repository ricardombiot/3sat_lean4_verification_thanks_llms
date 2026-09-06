-- lean_project/AbsSat/GraphPath/Model/Up.lean
import AbsSat.GraphPath.Model.Join

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

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- The `PathNodeId` `addNode` creates. -/
def newPid (g : GPathM) (d : NodeId) : PathNodeId := { id := d, parent_id := g.map_parent }

def newParents (g : GPathM) : List PathNodeId :=
  if g.current_step > 0 then (g.line (g.current_step - 1)).map (·.id) else []

def upNode (g : GPathM) (d : NodeId) (title : String) : PNodeM :=
  { id := newPid g d, title := title, parents := newParents g, sons := [], owners := g.gowners }

def upSons (g : GPathM) (d : NodeId) (n : PNodeM) : PNodeM :=
  if (newParents g).contains n.id then { n with sons := n.sons ++ [newPid g d] } else n

def addOwner (pid : PathNodeId) (n : PNodeM) : PNodeM :=
  { n with owners := n.owners ++ [pid] }

/-- What `addNode` does to every pre-existing node: it may gain the new node as
a son, and always gains it as an owner. The new node itself only gets the
owner, not the son — it is appended after the sons pass. -/
def upMap (g : GPathM) (d : NodeId) (n : PNodeM) : PNodeM :=
  addOwner (newPid g d) (upSons g d n)

theorem upMap_id (g : GPathM) (d : NodeId) (n : PNodeM) : (upMap g d n).id = n.id := by
  simp only [upMap, upSons, addOwner]; split <;> rfl

theorem upMap_parents (g : GPathM) (d : NodeId) (n : PNodeM) :
    (upMap g d n).parents = n.parents := by
  simp only [upMap, upSons, addOwner]; split <;> rfl

theorem upMap_owners (g : GPathM) (d : NodeId) (n : PNodeM) :
    (upMap g d n).owners = n.owners ++ [newPid g d] := by
  simp only [upMap, upSons, addOwner]; split <;> rfl

theorem addNode_nodes (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).nodes =
      g.nodes.map (upMap g d) ++ [addOwner (newPid g d) (upNode g d title)] := by
  show ((g.nodes.map (upSons g d)) ++ [upNode g d title]).map (addOwner (newPid g d))
      = g.nodes.map (upMap g d) ++ [addOwner (newPid g d) (upNode g d title)]
  rw [List.map_append, List.map_map]
  rfl

theorem addNode_current (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).current_step = g.current_step + 1 := rfl

-- ============================================================
-- `node?` through addNode
-- ============================================================

theorem addNode_node?_old (g : GPathM) (d : NodeId) (title : String)
    (pid' : PathNodeId) (n : PNodeM) (hn : g.node? pid' = some n) :
    (addNode g d title).node? pid' = some (upMap g d n) := by
  have hp : (fun x : PNodeM => (upMap g d x).id == pid') = (fun x : PNodeM => x.id == pid') := by
    funext x; rw [upMap_id]
  simp only [node?, addNode_nodes, List.find?_append, List.find?_map, Function.comp_def, hp]
  rw [show g.nodes.find? (fun x : PNodeM => x.id == pid') = some n from hn]
  rfl

/-- Below the new step, the extended graph has exactly `g`'s nodes. -/
theorem addNode_node?_below (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (pid' : PathNodeId) (n' : PNodeM)
    (hn' : (addNode g d title).node? pid' = some n')
    (hstep : pid'.id.step < g.current_step) :
    ∃ n, g.node? pid' = some n ∧ n' = upMap g d n := by
  have hmem : n' ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn'
  have hid : n'.id = pid' := node?_id_eq _ pid' n' hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hnid : n.id = pid' := by rw [← hid, ← hEq, upMap_id]
    have hsome : (g.node? n.id).isSome := node?_isSome_of_mem g n hn
    rw [hnid] at hsome
    obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨n₀, hn₀, ?_⟩
    have := addNode_node?_old g d title pid' n₀ hn₀
    rw [hn'] at this
    exact (Option.some.inj this)
  · simp only [List.mem_singleton] at hr
    exfalso
    have : n'.id = newPid g d := by rw [hr]; rfl
    rw [hid] at this
    rw [this] at hstep
    simp only [newPid] at hstep
    omega

-- ============================================================
-- Restricting a chain of the extended graph
-- ============================================================

theorem IsChain_of_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (sel : Int → PathNodeId)
    (h : IsChain (addNode g d title) sel) : IsChain g sel := by
  constructor
  · intro k hlo hhi
    obtain ⟨hsome, hstep⟩ := h.1 k hlo (by rw [addNode_current]; omega)
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨n, hn, _⟩ := addNode_node?_below g d title hd _ n' hn' (by rw [hstep]; exact hhi)
    exact ⟨by rw [hn]; rfl, hstep⟩
  · intro k hlo hhi
    have hstep := (h.1 (k + 1) (by omega) (by rw [addNode_current]; omega)).2
    have hlink := h.2 k hlo (by rw [addNode_current]; omega)
    cases hn' : (addNode g d title).node? (sel (k + 1)) with
    | none => rw [hn'] at hlink; exact absurd hlink List.not_mem_nil
    | some n' =>
      obtain ⟨n, hn, hEq⟩ :=
        addNode_node?_below g d title hd _ n' hn' (by rw [hstep]; omega)
      rw [hn'] at hlink
      rw [hn]
      simpa [hEq, upMap_parents] using hlink

theorem PairwiseOwned_of_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (sel : Int → PathNodeId)
    (hchain : IsChain (addNode g d title) sel)
    (h : PairwiseOwned (addNode g d title) sel) : PairwiseOwned g sel := by
  intro i j hi hj hi' hj' hne
  have hmem := h i j hi hj (by rw [addNode_current]; omega) (by rw [addNode_current]; omega) hne
  have hstepi := (hchain.1 i hi (by rw [addNode_current]; omega)).2
  have hstepj := (hchain.1 j hj (by rw [addNode_current]; omega)).2
  simp only [ownersAt, List.mem_filter] at hmem ⊢
  obtain ⟨hown, hstep⟩ := hmem
  refine ⟨?_, hstep⟩
  simp only [ownersOf] at hown ⊢
  cases hn' : (addNode g d title).node? (sel j) with
  | none => rw [hn'] at hown; exact absurd hown List.not_mem_nil
  | some n' =>
    obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title hd _ n' hn' (by rw [hstepj]; exact hj')
    rw [hn'] at hown
    rw [hn]
    dsimp only at hown ⊢
    rw [hEq, upMap_owners] at hown
    rcases List.mem_append.mp hown with hl | hr
    · exact hl
    · exfalso
      simp only [List.mem_singleton] at hr
      rw [hr] at hstepi
      simp only [newPid] at hstepi
      omega

-- ============================================================
-- The new node is what every chain selects at the top step
-- ============================================================

theorem chain_top_is_new (g : GPathM) (d : NodeId) (title : String)
    (hpos : 0 ≤ g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (sel : Int → PathNodeId) (h : IsChain (addNode g d title) sel) :
    sel g.current_step = newPid g d := by
  obtain ⟨hsome, hstep⟩ := h.1 g.current_step hpos (by rw [addNode_current]; omega)
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
  have hid : n'.id = sel g.current_step := node?_id_eq _ _ n' hn'
  have hmem : n' ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · exfalso
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hlt := hbelow n hn
    have hnn : n'.id = n.id := by rw [← hEq, upMap_id]
    rw [← hnn, hid] at hlt
    omega
  · simp only [List.mem_singleton] at hr
    rw [← hid, hr]
    rfl

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

theorem pathOf_addNode (g : GPathM) (d : NodeId) (title : String)
    (hpos : 0 ≤ g.current_step) (sel : Int → PathNodeId) :
    pathOf sel (addNode g d title) = (sel g.current_step).id :: pathOf sel g := by
  simp only [pathOf, addNode_current]
  rw [show g.current_step + 1 - 1 = g.current_step from by omega,
      intRange_zero_succ g.current_step hpos]
  simp

-- ============================================================
-- L3, soundness direction
-- ============================================================

/-- **L3 ⊆, for the `addNode` half of UP.** Every path the extended graph
denotes is `d` followed by a path the base graph denotes: the top line holds
exactly one node, so every chain is forced to select it there, and the rest of
the chain is a chain of the base graph. -/
theorem denot_addNode (g : GPathM) (d : NodeId) (title : String)
    (hpos : 0 ≤ g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (p : List NodeId) (h : denot (addNode g d title) p) :
    ∃ p', p = d :: p' ∧ denot g p' := by
  obtain ⟨sel, hchain, howned, hpath⟩ := h
  refine ⟨pathOf sel g, ?_, sel, IsChain_of_addNode g d title hd sel hchain,
    PairwiseOwned_of_addNode g d title hd sel hchain howned, rfl⟩
  rw [hpath, pathOf_addNode g d title hpos sel,
      chain_top_is_new g d title hpos hbelow sel hchain]
  rfl

/-- **L3 ⊆, as the machine calls it.** -/
theorem denot_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (hvalid : isValid (filterAll g reqs) = true)
    (hpos : 0 ≤ g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes, n.id.id.step < (filterAll g reqs).current_step)
    (p : List NodeId) (h : denot (upFiltering g reqs d title) p) :
    ∃ p', p = d :: p' ∧ denot (filterAll g reqs) p' := by
  have hstep : (filterAll g reqs).current_step = g.current_step :=
    (pruned_filterAll g reqs).step_eq
  have hshape : upFiltering g reqs d title = addNode (filterAll g reqs) d title := by
    simp only [upFiltering, up, hvalid, if_pos]
  rw [hshape] at h
  exact denot_addNode _ d title (by omega) (by omega) hbelow p h

/-- **L3 ⊆, all the way back to the unfiltered graph.** Needs `NodupIds` for
the same reason `denot_filterAll_subset` does: `node?` takes the first match,
so pruning can shadow a node if ids repeat. -/
theorem denot_upFiltering_base (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (hvalid : isValid (filterAll g reqs) = true)
    (hpos : 0 ≤ g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes, n.id.id.step < (filterAll g reqs).current_step)
    (hnd : NodupIds g)
    (p : List NodeId) (h : denot (upFiltering g reqs d title) p) :
    ∃ p', p = d :: p' ∧ denot g p' := by
  obtain ⟨p', hp, hden⟩ := denot_upFiltering g reqs d title hvalid hpos hd hbelow p h
  exact ⟨p', hp, denot_filterAll_subset g hnd reqs p' hden⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.denot_upFiltering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_upFiltering

/-- info: 'AbsSat.GraphPath.Model.denot_upFiltering_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_upFiltering_base

end AbsSat.GraphPath.Model
