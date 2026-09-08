-- lean_project/AbsSat/GraphPath/Model/AddNode.lean
import AbsSat.GraphPath.Model.Coherence

/-!
`addNode` in `ChainSound` currency — the gap `Coherence.lean` named — plus the
statement of L6's `up` case that turns out to be the correct one.

## `MachineOk`

`ChainSound`'s `root_shape` field says only the step-0 node is a root, and the
new node's `parent_id` is exactly `g.map_parent`. So `addNode` can only
establish it if `map_parent` says what it is supposed to say: `none` before
anything has been visited, `some` after. That is `MachineOk`, and every
machine operation maintains it — `addNode` sets it, and everything else is a
`Pruned` step, which now carries `map_parent_eq`.

## The correction to `L6Up.lean`

`L6Up.lean` framed the `up` case as "`SupportedG` is preserved", and observed
that the `gowners` field is *not* preserved by `filterRequire` alone. That
observation was right and the framing was wrong: pruning `gowners` is
*supposed* to kill chains — the ones that do not satisfy the requirement.

The correct statement is not that every chain survives, but that the right
ones do:

    ChainSound_filterRequire :
      ChainSound g sel → (sel req.step).id = req → ChainSound (filterRequire g req) sel

and everything else about the chain passes through untouched, because
`filterRequire` only rewrites `gowners`. Folded over the requirement list and
composed with `ChainSound_review`, that gives `ChainSound_filterAll`: **a chain
that satisfies the requirements survives the whole filter**. This is L2's ⊇
direction, and L3's, in the form they were always meant to have.

`ChainSound_upFiltering` then adds the new node on top, via
`ChainSound_addNode`.

## Where L6 stands after this

Three of the four preservation obligations are now in `ChainSound` currency:
`ChainSound_initSeed` (seed), `ChainSound_upFiltering` (up),
`ChainSound_review` (review, in `Coherence.lean`). The join case is still only
in `ChainG` currency (`Join.Supported_join`): lifting it needs `Grown`
extended to track sons and global owners as well as owners and parents, which
is the same small piece of work `Pruned` needed twice already.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- The shape facts about `current_step` / `map_parent` that `addNode` needs
and that every machine operation maintains. `map_parent` is exactly "the map
node the last `up` visited", so it is `none` iff nothing has been visited. -/
def MachineOk (g : GPathM) : Prop :=
  0 ≤ g.current_step ∧ (g.current_step = 0 → g.map_parent = none)
    ∧ (0 < g.current_step → g.map_parent ≠ none)

theorem addNode_map_parent (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).map_parent = some d := rfl

theorem MachineOk_empty : MachineOk empty := by
  simp [MachineOk, empty]

theorem MachineOk_addNode (g : GPathM) (d : NodeId) (title : String)
    (h : MachineOk g) : MachineOk (addNode g d title) := by
  obtain ⟨h0, _, _⟩ := h
  refine ⟨by rw [addNode_current]; omega, ?_, ?_⟩
  · intro hz; rw [addNode_current] at hz; omega
  · intro _; rw [addNode_map_parent]; simp

theorem MachineOk_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : MachineOk g) :
    MachineOk g' := by
  obtain ⟨h0, hz, hp⟩ := h
  rw [MachineOk, hpr.step_eq, hpr.map_parent_eq]
  exact ⟨h0, hz, hp⟩

-- ============================================================
-- What `addNode` does to sons
-- ============================================================

theorem upMap_sons (g : GPathM) (d : NodeId) (n : PNodeM) :
    (upMap g d n).sons = (upSons g d n).sons := rfl

theorem mem_upSons_sons (g : GPathM) (d : NodeId) (n : PNodeM) (q : PathNodeId)
    (hq : q ∈ n.sons) : q ∈ (upSons g d n).sons := by
  simp only [upSons]
  split
  · exact List.mem_append_left _ hq
  · exact hq

theorem newPid_mem_upSons_sons (g : GPathM) (d : NodeId) (n : PNodeM)
    (hc : (newParents g).contains n.id = true) :
    newPid g d ∈ (upSons g d n).sons := by
  simp only [upSons, hc]
  exact List.mem_append_right _ (by simp)

-- ============================================================
-- addNode establishes the three extra ChainSound fields
-- ============================================================

theorem ChainSound_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g)
    (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (addNode g d title) (extend g d sel) := by
  obtain ⟨h0, hz, hposmp⟩ := hmok
  have hnew := addNode_node?_new g d title hd hbelow
  refine ⟨ChainG_addNode g d title hd hbelow sel h.chain, ?_, ?_, ?_⟩
  · -- self_owned: the new node's owners are exactly the global owners plus itself
    intro k hlo hhi
    rw [addNode_current] at hhi
    rcases int_eq_or_ne k g.current_step with hk | hk
    · subst hk
      rw [extend_top]
      simp only [ownersOf, hnew, addOwner, upNode]
      exact List.mem_append_right _ (by simp)
    · have hlt : k < g.current_step := by omega
      rw [extend_below g d sel k hlt]
      have hs := h.self_owned k hlo hlt
      simp only [ownersOf] at hs ⊢
      cases hn : g.node? (sel k) with
      | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
      | some n =>
        rw [hn] at hs
        rw [addNode_node?_old g d title _ n hn]
        simp only [upMap_owners]
        exact List.mem_append_left _ hs
  · -- son_link: the top old node gains the new one as a son
    intro k hlo hhi
    rw [addNode_current] at hhi
    rcases int_eq_or_ne (k + 1) g.current_step with hk | hk
    · rw [hk, extend_top, extend_below g d sel k (by omega)]
      obtain ⟨hsome, _⟩ := h.chain.1.1 k hlo (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      simp only [sonsOf, addNode_node?_old g d title _ n hn, upMap_sons]
      refine newPid_mem_upSons_sons g d n ?_
      have hmem : sel k ∈ (g.line (g.current_step - 1)).map (·.id) :=
        mem_line_of_node? g (sel k) n hn (g.current_step - 1)
          (by rw [(h.chain.1.1 k hlo (by omega)).2]; omega)
      rw [node?_id_eq g (sel k) n hn]
      simp only [newParents, if_pos (show g.current_step > 0 by omega)]
      exact List.elem_eq_true_of_mem hmem
    · have hlt : k + 1 < g.current_step := by omega
      rw [extend_below g d sel k (by omega), extend_below g d sel (k + 1) hlt]
      have hs := h.son_link k hlo hlt
      simp only [sonsOf] at hs ⊢
      cases hn : g.node? (sel k) with
      | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
      | some n =>
        rw [hn] at hs
        rw [addNode_node?_old g d title _ n hn]
        simp only [upMap_sons]
        exact mem_upSons_sons g d n _ hs
  · -- root_shape: this is what `MachineOk` is for
    constructor
    · rcases int_eq_or_ne (0 : Int) g.current_step with hz0 | hz0
      · simp only [extend, if_pos hz0, newPid]
        exact hz hz0.symm
      · rw [extend_below g d sel 0 (by omega)]
        exact h.root_shape.1
    · intro k hk hhi
      rw [addNode_current] at hhi
      rcases int_eq_or_ne k g.current_step with hkc | hkc
      · subst hkc
        rw [extend_top]
        simp only [newPid]
        exact hposmp (by omega)
      · rw [extend_below g d sel k (by omega)]
        exact h.root_shape.2 k hk (by omega)

-- ============================================================
-- Which chains survive the filter
-- ============================================================

/-- **L2's ⊇ direction, for one requirement.** `filterRequire` rewrites
`gowners` only, so everything about a chain survives it *except* the
"every chain node is a global owner" field — and that one survives exactly
when the chain goes through the required node. Which is the correct answer:
a chain that does not satisfy the requirement is one the filter is *meant*
to kill. -/
theorem ChainSound_filterRequire (g : GPathM) (req : NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hreq : 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (filterRequire g req) sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨hchain, howned, ?_⟩, hself, hson, hroot⟩
  intro k hlo hhi
  simp only [filterRequire, List.mem_filter]
  refine ⟨hgow k hlo hhi, ?_⟩
  have hstepk := (hchain.1 k hlo hhi).2
  rcases int_eq_or_ne k req.step with hk | hk
  · subst hk
    have hid : (sel req.step).id = req := hreq hlo hhi
    simp only [Bool.or_eq_true]
    exact Or.inr (by rw [hid]; exact beq_iff_eq.mpr rfl)
  · simp only [Bool.or_eq_true]
    refine Or.inl ?_
    simp only [bne_iff_ne, hstepk]
    exact hk

theorem ChainSound_foldl_filterRequire (reqs : List NodeId) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      (∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) →
      ChainSound (reqs.foldl filterRequire g) sel := by
  induction reqs with
  | nil => intro g sel h _; simpa using h
  | cons req rest ih =>
    intro g sel h hreqs
    simp only [List.foldl_cons]
    exact ih _ sel
      (ChainSound_filterRequire g req sel h (hreqs req List.mem_cons_self))
      (fun r hr => hreqs r (List.mem_cons_of_mem _ hr))

/-- **A chain that satisfies the requirements survives the whole filter.** -/
theorem ChainSound_filterAll (g : GPathM) (reqs : List NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hreqs : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (filterAll g reqs) sel :=
  ChainSound_review _ sel (ChainSound_foldl_filterRequire reqs g sel h hreqs)

/-- **L6's `up` case, in its correct form.** A chain that satisfies the
requirements survives `upFiltering`, extended by the new node. -/
theorem ChainSound_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (hvalid : isValid (filterAll g reqs) = true)
    (hd : d.step = (filterAll g reqs).current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes,
      n.id.id.step < (filterAll g reqs).current_step)
    (hmok : MachineOk (filterAll g reqs))
    (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hreqs : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (upFiltering g reqs d title) (extend (filterAll g reqs) d sel) := by
  have hshape : upFiltering g reqs d title = addNode (filterAll g reqs) d title := by
    simp only [upFiltering, up, hvalid, if_pos]
  rw [hshape]
  exact ChainSound_addNode _ d title hd hbelow hmok sel
    (ChainSound_filterAll g reqs sel h hreqs)

/-- **L6's seed case, in `ChainSound` currency.** -/
theorem ChainSound_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    ChainSound (GPathM.initSeed d title) (fun _ => { id := d, parent_id := none }) := by
  have hnodes := initSeed_nodes d title
  have hcur := initSeed_current d title
  have hnode : (GPathM.initSeed d title).node? { id := d, parent_id := none }
      = some (PNodeM.mk { id := d, parent_id := none } title [] []
          [{ id := d, parent_id := none }]) := by
    simp only [node?, hnodes, List.find?_cons, beq_self_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k hlo hhi
    rw [hcur] at hhi
    exact ⟨by rw [hnode]; rfl, by show d.step = k; omega⟩
  · intro k hlo hhi; rw [hcur] at hhi; omega
  · intro i j hi hj hi' hj' hne; rw [hcur] at hi' hj'; omega
  · intro k hlo hhi
    show _ ∈ (GPathM.initSeed d title).gowners
    unfold GPathM.initSeed GPathM.up GPathM.addNode
    simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry]
  · intro k hlo hhi
    simp only [ownersOf, hnode]
    simp
  · intro k hlo hhi; rw [hcur] at hhi; omega
  · exact ⟨rfl, fun k hk hk' => by rw [hcur] at hk'; omega⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ChainSound_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_addNode

/-- info: 'AbsSat.GraphPath.Model.ChainSound_upFiltering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_upFiltering

/-- info: 'AbsSat.GraphPath.Model.ChainSound_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_initSeed

end AbsSat.GraphPath.Model
