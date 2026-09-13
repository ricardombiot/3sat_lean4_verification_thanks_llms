-- lean_project/AbsSat/GraphPath/Model/SubsetSemantics.lean
import AbsSat.GraphPath.Model.UnitPropagation
import AbsSat.GraphPath.Model.Reader
import AbsSat.GraphPath.Model.Sons
import AbsSat.GraphPath.Model.PrefixDecode

/-!
# A state is a subset of partial paths, and the operations are set operations

The author's framing: the machine does not reason about individual owner facts; each
state is a **subset of partially built paths**, and the operations are set operations.
In those terms the Helly gap does not appear inside the operations — a path either
goes through every pin or it does not.

* `denotS g p` — the subset a state holds: the paths of its sound chains.
* **filter** — `denotS_filterAll`: for a reachable state whose filter is valid,
  `denotS (filterAll g reqs) = denotS g ∩ {paths through every pin}`, exactly.
* **extension** — `denotS_addNode`, `denotS_upFiltering`: `up` appends the new node to
  every path of the subset, exactly; with the filter in front,
  `denotS (upFiltering g reqs d) = {d :: p | p ∈ denotS g, p through every pin}`.
* **union** — `denotS_join_union`: `denotS g₁ ∪ denotS g₂ ⊆ denotS (join g₁ g₂)`. Equality
  is not claimed: a join can form chains that mix both sides. `denotS_sound` shows that
  whatever a state's subset holds, mixed paths included, is a partial solution.

What stays open is not here: the machine tests a subset for emptiness by looking at
`isValid` on its compressed owner tables, not at the subset.
-/

namespace AbsSat.GraphPath.Model.SubsetSemantics

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.CnfChain
open AbsSat.GraphPath.Model.PrefixConservation
open AbsSat.GraphPath.Model.UnitPropagation

/-- The subset of partial paths a state holds: the paths of its sound chains. -/
def denotS (g : GPathM) (p : List NodeId) : Prop := ∃ sel, ChainSound g sel ∧ p = pathOf sel g

-- ============================================================
-- Filter: an exact intersection
-- ============================================================

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

-- ============================================================
-- Extension: `up` appends the new node to every path
-- ============================================================

theorem MachineOk_reachable (reqOf : NodeId → List NodeId) (g : GPathM)
    (h : Reachable reqOf g) : MachineOk g := by
  induction h with
  | seed d title _ _ => exact Certifies.MachineOk_initSeed d title
  | up g d title _ _ _ _ ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show MachineOk (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact MachineOk_addNode _ d title (MachineOk_of_pruned hpr ih)
    · exact MachineOk_of_pruned hpr ih
  | join g₁ g₂ _ _ _ ih₁ _ => exact Certifies.MachineOk_join g₁ g₂ ih₁

theorem mem_upSons_sons_cases (g : GPathM) (d : NodeId) (n : PNodeM) (q : PathNodeId)
    (hq : q ∈ (upSons g d n).sons) : q ∈ n.sons ∨ q = newPid g d := by
  simp only [upSons] at hq
  split at hq
  · rcases List.mem_append.mp hq with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)
  · exact Or.inl hq

/-- A sound chain of the extended state, read below the new step, is a sound chain of
the state before `addNode`. -/
theorem ChainSound_of_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (sel : Int → PathNodeId)
    (h : ChainSound (addNode g d title) sel) : ChainSound g sel := by
  obtain ⟨hchainA, hownedA, hgowA⟩ := h.chain
  have hchain := IsChain_of_addNode g d title hd sel hchainA
  have hne : ∀ k, 0 ≤ k → k < g.current_step → sel k ≠ newPid g d := by
    intro k h0 hk heq
    have hstep := (hchain.1 k h0 hk).2
    rw [heq] at hstep
    simp only [newPid] at hstep
    omega
  refine ⟨⟨hchain, PairwiseOwned_of_addNode g d title hd sel hchainA hownedA, ?_⟩, ?_, ?_, ?_⟩
  · intro k h0 hk
    have hm : sel k ∈ g.gowners ++ [newPid g d] := hgowA k h0 (by rw [addNode_current]; omega)
    rcases List.mem_append.mp hm with h1 | h1
    · exact h1
    · exact absurd (List.mem_singleton.mp h1) (hne k h0 hk)
  · intro k h0 hk
    have hso := h.self_owned k h0 (by rw [addNode_current]; omega)
    have hstep := (hchainA.1 k h0 (by rw [addNode_current]; omega)).2
    simp only [ownersOf] at hso ⊢
    cases hn' : (addNode g d title).node? (sel k) with
    | none => rw [hn'] at hso; exact absurd hso List.not_mem_nil
    | some n' =>
      obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title hd _ n' hn' (by rw [hstep]; exact hk)
      rw [hn'] at hso
      rw [hn]
      dsimp only at hso ⊢
      rw [hEq, upMap_owners] at hso
      rcases List.mem_append.mp hso with h1 | h1
      · exact h1
      · exact absurd (List.mem_singleton.mp h1) (hne k h0 hk)
  · intro k h0 hk
    have hsl := h.son_link k h0 (by rw [addNode_current]; omega)
    have hstep := (hchainA.1 k h0 (by rw [addNode_current]; omega)).2
    simp only [sonsOf] at hsl ⊢
    cases hn' : (addNode g d title).node? (sel k) with
    | none => rw [hn'] at hsl; exact absurd hsl List.not_mem_nil
    | some n' =>
      obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title hd _ n' hn' (by rw [hstep]; omega)
      rw [hn'] at hsl
      rw [hn]
      dsimp only at hsl ⊢
      rw [hEq, upMap_sons] at hsl
      rcases mem_upSons_sons_cases g d n _ hsl with h1 | h1
      · exact h1
      · exact absurd h1 (hne (k + 1) (by omega) hk)
  · obtain ⟨hr0, hr⟩ := h.root_shape
    exact ⟨hr0, fun k hk hk' => hr k hk (by rw [addNode_current]; omega)⟩

/-- **`addNode` is an exact extension of the subset.** -/
theorem denotS_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (p : List NodeId) :
    denotS (addNode g d title) p ↔ ∃ p', p = d :: p' ∧ denotS g p' := by
  constructor
  · rintro ⟨sel, hs, rfl⟩
    obtain ⟨hchainA, _, _⟩ := hs.chain
    refine ⟨pathOf sel g, ?_, sel, ChainSound_of_addNode g d title hd sel hs, rfl⟩
    rw [pathOf_addNode g d title hmok.1 sel, chain_top_is_new g d title hmok.1 hbelow sel hchainA]
      <;> rfl
  · rintro ⟨p', rfl, sel, hs, rfl⟩
    refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hs, ?_⟩
    have hpath : pathOf (extend g d sel) g = pathOf sel g := by
      simp only [pathOf]
      refine List.map_congr_left ?_
      intro k hk
      have hk1 := mem_intRange_upper (List.mem_reverse.mp hk)
      rw [extend_below g d sel k (by omega)]
    rw [pathOf_addNode g d title hmok.1, extend_top, hpath] <;> rfl

/-- **`upFiltering` is filter-then-extend, exactly.** For a reachable state whose filter
is valid, the subset after `upFiltering` is `d` prepended to every path of the old
subset that goes through every pin. -/
theorem denotS_upFiltering (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (d : NodeId) (title : String)
    (hvalid : isValid (filterAll g reqs) = true) (hd : d.step = g.current_step)
    (p : List NodeId) :
    denotS (upFiltering g reqs d title) p ↔
      ∃ p', p = d :: p' ∧ denotS g p' ∧
        ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → req ∈ p' := by
  have hpr := pruned_filterAll g reqs
  have hshape : upFiltering g reqs d title = addNode (filterAll g reqs) d title := by
    simp only [upFiltering, GPathM.up, hvalid, if_pos]
  rw [hshape, denotS_addNode (filterAll g reqs) d title (by rw [hpr.step_eq]; exact hd)
    (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr))
    (MachineOk_of_pruned hpr (MachineOk_reachable reqOf g hr))]
  constructor
  · rintro ⟨p', rfl, hp'⟩
    exact ⟨p', rfl, (denotS_filterAll reqOf g hr reqs hvalid p').mp hp'⟩
  · rintro ⟨p', rfl, hp', hthrough⟩
    exact ⟨p', rfl, (denotS_filterAll reqOf g hr reqs hvalid p').mpr ⟨hp', hthrough⟩⟩

-- ============================================================
-- Union: `join` holds both subsets
-- ============================================================

theorem denotS_join_of_left (g₁ g₂ : GPathM) (p : List NodeId) (h : denotS g₁ p) :
    denotS (join g₁ g₂) p := by
  obtain ⟨sel, hs, rfl⟩ := h
  exact ⟨sel, ChainSound_join_left g₁ g₂ sel hs, by simp only [pathOf, (grown_join_left g₁ g₂).step_eq]⟩

theorem denotS_join_of_right (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (p : List NodeId)
    (h : denotS g₂ p) : denotS (join g₁ g₂) p := by
  obtain ⟨sel, hs, rfl⟩ := h
  exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hs,
    by simp only [pathOf, (grown_join_right g₁ g₂ hok).step_eq]⟩

/-- **`join` holds the union of both subsets.** Equality is not claimed: a join can form
chains that mix both sides (see `denotS_sound`). -/
theorem denotS_join_union (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (p : List NodeId)
    (h : denotS g₁ p ∨ denotS g₂ p) : denotS (join g₁ g₂) p :=
  h.elim (denotS_join_of_left g₁ g₂ p) (denotS_join_of_right g₁ g₂ hok p)

/-- **Whatever a subset holds is a partial solution**, including paths a join mixes from
both sides. -/
theorem denotS_sound (φ : Cnf) (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (p : List NodeId) (hp : denotS g p) :
    ∃ sel, p = pathOf sel g ∧ SatUpTo φ (decode sel) (g.current_step - 1) := by
  obtain ⟨sel, hs, rfl⟩ := hp
  obtain ⟨hchain, howned, _⟩ := hs.chain
  exact ⟨sel, rfl, PrefixDecode.satUpTo_of_chain φ hwf g hmr sel hchain howned⟩

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.ChainSound_of_pruned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_of_pruned

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.denotS_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denotS_filterAll

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.ChainSound_of_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_of_addNode

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.denotS_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denotS_addNode

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.denotS_upFiltering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denotS_upFiltering

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.denotS_join_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denotS_join_union

/-- info: 'AbsSat.GraphPath.Model.SubsetSemantics.denotS_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denotS_sound

end AbsSat.GraphPath.Model.SubsetSemantics
