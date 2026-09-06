-- lean_project/AbsSat/GraphPath/Model/L6Up.lean
import AbsSat.GraphPath.Model.Up

/-!
**L6's `up` case, reduced to a single statement.**

`upFiltering g reqs d title` is `up (filterAll g reqs) d title`, i.e. three
things in sequence: a fold of `filterRequire`, then `review`, then `addNode`.
This module proves the first and the third, leaving exactly the second.

* **`filterRequire`** rewrites `gowners` only, and `Supported` never reads it:
  `Supported_filterRequire` is `Iff.rfl`. Free.
* **`addNode`** is `SupportedG_addNode`, proved here by an explicit
  chain-extension construction (`ChainG_addNode`): take the base graph's chain
  and select the new node at the new top step. Below the new step nothing
  moved; at the new step the single new node is forced.
* **`review`** is not proved, and it is the whole of L6.

**Why `SupportedG` and not `Supported`.** `addNode` hands the new node exactly
`gowners` as its owners. So for the new node to *co-own* an existing chain,
that chain must live inside `gowners`. `ChainG` carries that condition, and
`SupportedG`/`InhabitedG` are the two forms in which it has to travel: a node
needs a chain through it, and the new node needs *some* chain to attach to.
`InhabitedG` is the second half of L6 (`valid ⇒ denot ≠ ∅`), so the two halves
genuinely feed each other rather than being independent goals.

This condition is not preserved by `filterRequire` in isolation — pruning
`gowners` can drop a chain node — which is precisely why the induction must be
run over the whole `upFiltering` composite and not step by step, and why
`review` is where everything lands.

**The remaining hole, stated once:**

    SupportedG g → SupportedG (review g)        (with InhabitedG alongside)

That is the same sentence as L2's ⊇ direction and as L3's ⊇ direction. All
three of the bridge's open ends are this one statement.

**Empirical status.** `lake exe l6search` now inspects every state the machine
holds at every step, not just the last: 1,680 states over 150 synthetic maps
with arbitrary backward, step-distinct requirements and no 3SAT structure.
Every valid one had a complete co-owned chain.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- Decidable case split on `Int` equality. `by_cases` routes through
`Classical.choice`, which would widen every axiom closure in this file. -/
private theorem int_eq_or_ne (a b : Int) : a = b ∨ a ≠ b := by
  cases h : (a == b) with
  | true => exact Or.inl (eq_of_beq h)
  | false =>
    refine Or.inr (fun heq => ?_)
    rw [heq, beq_iff_eq.mpr (rfl : b = b)] at h
    exact Bool.noConfusion h

/-- A chain, together with the extra condition that every node it selects is a
*global* owner. `addNode` hands the new node exactly `gowners` as its owners,
so the new node can co-own a chain only if the chain lives inside `gowners`. -/
def ChainG (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  IsChain g sel ∧ PairwiseOwned g sel ∧
    ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ g.gowners

def SupportedG (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n → ∃ sel, ChainG g sel ∧ sel pid.id.step = pid

def InhabitedG (g : GPathM) : Prop := ∃ sel, ChainG g sel

/-- `filterRequire` rewrites `gowners` only, and `Supported` never reads it. -/
theorem Supported_filterRequire (g : GPathM) (req : NodeId) :
    Supported (filterRequire g req) ↔ Supported g := Iff.rfl

def extend (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) : Int → PathNodeId :=
  fun k => if k = g.current_step then newPid g d else sel k

theorem extend_top (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) :
    extend g d sel g.current_step = newPid g d := by simp [extend]

theorem extend_below (g : GPathM) (d : NodeId) (sel : Int → PathNodeId)
    (k : Int) (h : k < g.current_step) : extend g d sel k = sel k := by
  simp [extend, Int.ne_of_lt h]

theorem addNode_node?_new (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) :
    (addNode g d title).node? (newPid g d)
      = some (addOwner (newPid g d) (upNode g d title)) := by
  have hnone : g.nodes.find? (fun x : PNodeM => x.id == newPid g d) = none := by
    rw [List.find?_eq_none]
    intro x hx hbeq
    have hxid : x.id = newPid g d := eq_of_beq hbeq
    have := hbelow x hx
    rw [hxid] at this
    simp only [newPid] at this
    omega
  have hp : (fun x : PNodeM => (upMap g d x).id == newPid g d)
      = (fun x : PNodeM => x.id == newPid g d) := by funext x; rw [upMap_id]
  simp only [node?, addNode_nodes, List.find?_append, List.find?_map, Function.comp_def, hp,
    hnone, Option.map_none, Option.none_or]
  simp [addOwner, upNode, newPid]

theorem addNode_gowners (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).gowners = g.gowners ++ [newPid g d] := rfl

theorem mem_line_of_node? (g : GPathM) (pid : PathNodeId) (n : PNodeM)
    (hn : g.node? pid = some n) (k : Int) (hstep : pid.id.step = k) :
    pid ∈ (g.line k).map (·.id) := by
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq g pid n hn
  have : n ∈ g.line k := by
    simp only [line, List.mem_filter]
    exact ⟨hmem, by rw [hid, hstep]; exact beq_iff_eq.mpr rfl⟩
  have := List.mem_map_of_mem (f := fun m : PNodeM => m.id) this
  rwa [hid] at this

/-- **The chain-extension construction.** A chain of the base graph, extended
by the new node at the new top step, is a chain of the extended graph. -/
theorem ChainG_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (sel : Int → PathNodeId) (h : ChainG g sel) :
    ChainG (addNode g d title) (extend g d sel) := by
  obtain ⟨hchain, howned, hgow⟩ := h
  have hnew := addNode_node?_new g d title hd hbelow
  have hnewstep : (newPid g d).id.step = g.current_step := by simp only [newPid]; omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- IsChain, node existence and step
  · intro k hlo hhi
    rw [addNode_current] at hhi
    rcases int_eq_or_ne (k) (g.current_step) with hk | hk
    · subst hk
      rw [extend_top]
      exact ⟨by rw [hnew]; rfl, hnewstep⟩
    · have hlt : k < g.current_step := by omega
      rw [extend_below g d sel k hlt]
      obtain ⟨hsome, hstep⟩ := hchain.1 k hlo hlt
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨by rw [addNode_node?_old g d title _ n hn]; rfl, hstep⟩
  -- IsChain, parent links
  · intro k hlo hhi
    rw [addNode_current] at hhi
    rcases int_eq_or_ne (k + 1) (g.current_step) with hk | hk
    · rw [hk, extend_top, hnew, extend_below g d sel k (by omega)]
      simp only [Option.map_some, Option.getD_some, addOwner, upNode, newParents,
        if_pos (show g.current_step > 0 by omega)]
      obtain ⟨hsome, hstep⟩ := hchain.1 k hlo (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      exact mem_line_of_node? g (sel k) n hn (g.current_step - 1) (by omega)
    · have hlt : k + 1 < g.current_step := by omega
      rw [extend_below g d sel k (by omega), extend_below g d sel (k + 1) hlt]
      have hlink := hchain.2 k hlo hlt
      cases hn : g.node? (sel (k + 1)) with
      | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
      | some n =>
        rw [hn] at hlink
        rw [addNode_node?_old g d title _ n hn]
        simpa [upMap_parents] using hlink
  -- PairwiseOwned
  · intro i j hi hj hi' hj' hne
    rw [addNode_current] at hi' hj'
    simp only [ownersAt, List.mem_filter]
    rcases int_eq_or_ne (j) (g.current_step) with hjc | hjc
    · -- the other end is the new node: its owners are exactly the global owners
      subst hjc
      have hic : i < g.current_step := by omega
      rw [extend_below g d sel i hic, extend_top]
      simp only [ownersOf, hnew, addOwner, upNode]
      refine ⟨List.mem_append_left _ (hgow i hi hic), ?_⟩
      have hstepi := (hchain.1 i hi hic).2
      rw [hstepi]
      exact beq_iff_eq.mpr rfl
    · have hjlt : j < g.current_step := by omega
      rw [extend_below g d sel j hjlt]
      obtain ⟨hsome, hstepj⟩ := hchain.1 j hj hjlt
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      simp only [ownersOf, addNode_node?_old g d title _ n hn, upMap_owners]
      rcases int_eq_or_ne (i) (g.current_step) with hic | hic
      · subst hic
        rw [extend_top]
        exact ⟨List.mem_append_right _ (by simp), by rw [hnewstep]; exact beq_iff_eq.mpr rfl⟩
      · have hilt : i < g.current_step := by omega
        rw [extend_below g d sel i hilt]
        have hmem := howned i j hi hj hilt hjlt hne
        simp only [ownersAt, List.mem_filter, ownersOf, hn] at hmem
        exact ⟨List.mem_append_left _ hmem.1, hmem.2⟩
  -- every selected node is a global owner
  · intro k hlo hhi
    rw [addNode_current] at hhi
    rw [addNode_gowners]
    rcases int_eq_or_ne (k) (g.current_step) with hk | hk
    · subst hk; rw [extend_top]; exact List.mem_append_right _ (by simp)
    · have hlt : k < g.current_step := by omega
      rw [extend_below g d sel k hlt]
      exact List.mem_append_left _ (hgow k hlo hlt)

theorem InhabitedG_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (h : InhabitedG g) : InhabitedG (addNode g d title) := by
  obtain ⟨sel, hsel⟩ := h
  exact ⟨extend g d sel, ChainG_addNode g d title hd hbelow sel hsel⟩

/-- **L6's UP step, for `addNode`.** Adding a node preserves total support,
provided the base graph already had *some* admissible chain — the new node's
owners are exactly `gowners`, so it needs a chain living inside them to
co-own. That is why `SupportedG` and `InhabitedG` have to travel together. -/
theorem SupportedG_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hsup : SupportedG g) (hinh : InhabitedG g) : SupportedG (addNode g d title) := by
  intro pid n hn
  have hmem : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq _ pid n hn
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · -- an old node: reuse its chain, extended
    obtain ⟨n₁, hn₁, hEq⟩ := List.mem_map.mp hl
    have hsame : n.id = n₁.id := by rw [← hEq, upMap_id]
    have hstep : pid.id.step < g.current_step := by rw [← hid, hsame]; exact hbelow n₁ hn₁
    obtain ⟨n₀, hn₀, _⟩ := addNode_node?_below g d title hd pid n hn hstep
    obtain ⟨sel, hsel, htop⟩ := hsup pid n₀ hn₀
    refine ⟨extend g d sel, ChainG_addNode g d title hd hbelow sel hsel, ?_⟩
    rw [extend_below g d sel pid.id.step hstep]
    exact htop
  · -- the new node: any admissible chain of the base, extended
    simp only [List.mem_singleton] at hr
    have hpid : pid = newPid g d := by rw [← hid, hr]; rfl
    obtain ⟨sel, hsel⟩ := hinh
    refine ⟨extend g d sel, ChainG_addNode g d title hd hbelow sel hsel, ?_⟩
    rw [hpid]
    rw [show (newPid g d).id.step = g.current_step from by simp only [newPid]; exact hd]
    exact extend_top g d sel

/-- **L6's `up` case, reduced to the review step.** Everything the UP
constructor does *except* `review` preserves total support:

* the `filterRequire` fold rewrites `gowners` only, and `Supported` never
  reads it (`Supported_filterRequire`);
* `addNode` is `SupportedG_addNode` above.

So the whole `up` case of L6 rests on one statement, and only one:

    SupportedG g → SupportedG (review g)     (with InhabitedG alongside)

which is also L2's ⊇ direction. -/
theorem SupportedG_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (hvalid : isValid (filterAll g reqs) = true)
    (hd : d.step = (filterAll g reqs).current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes,
      n.id.id.step < (filterAll g reqs).current_step)
    (hsup : SupportedG (filterAll g reqs)) (hinh : InhabitedG (filterAll g reqs)) :
    SupportedG (upFiltering g reqs d title) := by
  have hshape : upFiltering g reqs d title = addNode (filterAll g reqs) d title := by
    simp only [upFiltering, up, hvalid, if_pos]
  rw [hshape]
  exact SupportedG_addNode _ d title hd hbelow hsup hinh

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ChainG_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainG_addNode

/-- info: 'AbsSat.GraphPath.Model.SupportedG_upFiltering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportedG_upFiltering

end AbsSat.GraphPath.Model
