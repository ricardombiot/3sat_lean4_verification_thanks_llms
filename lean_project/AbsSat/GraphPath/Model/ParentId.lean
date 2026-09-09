-- lean_project/AbsSat/GraphPath/Model/ParentId.lean
import AbsSat.GraphPath.Model.MapChain

/-!
**The local condition on `parent_id` — and a chain is determined by its map
ids.**

v33 sized the residual gap in `ReqSatImpliesOwned`: at a pinned step the owner
set holds at most two path nodes, both carrying the map id the requirement
names, differing only in `parent_id`. So the question is which parent.

`parent_id` is not decoration. `addNode` builds `⟨d, g.map_parent⟩`, where
`map_parent` is the map node the last `up` visited on that branch — and the
node's `parents` are exactly that branch's previous line. So:

* **`TL`** — the top line of a state carries the map node `map_parent` names;
* **`PMP`** — every parent of a node carries the map id the node's `parent_id`
  names.

From `PMP`, `IsChain`'s parent link turns into a statement about the ids
themselves: `(sel (k+1)).parent_id = some (sel k).id`. Together with
`root_shape` (v29) at step 0, that makes a chain **determined by its sequence
of map ids** — `chain_eq_of_mapIds_eq`.

Which sharpens v33: at a pinned step there is no choice between two path nodes
at all. The chain's pick is fixed by the map id the requirement names and the
map id of the step below. What is still missing is only that the fixed one is
in the owner list.
-/

namespace AbsSat.GraphPath.Model.ParentId

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- The top line carries `map_parent`
-- ============================================================

def TL (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, n.id.id.step = h.current_step - 1 → some n.id.id = h.map_parent

theorem TL_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : TL g) : TL g' := by
  intro n' hn' hstep
  obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
  rw [hpr.map_parent_eq, hid]
  exact h n hn (by rw [← hid, ← hpr.step_eq]; exact hstep)

theorem TL_addNode (g : GPathM) (d : NodeId) (title : String)
    (_hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) :
    TL (addNode g d title) := by
  intro n' hn' hstep
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    exfalso
    rw [← hEq, upMap_id] at hstep
    have := hbelow n hn
    have hc : (addNode g d title).current_step = g.current_step + 1 := rfl
    rw [hc] at hstep
    omega
  · rcases List.mem_singleton.mp hmem with rfl
    show some d = some d
    rfl

theorem TL_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : TL g₁) (h₂ : TL g₂) : TL (join g₁ g₂) := by
  have hstepeq : g₁.current_step = g₂.current_step :=
    eq_of_beq ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp hok).1).1).1
  have hmpeq : g₁.map_parent = g₂.map_parent :=
    eq_of_beq ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp hok).1).1).2
  intro n' hn' hstep
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    have hni : n'.id = n.id := by
      rw [← hEq]; cases g₂.node? n.id with | some q => rfl | none => rfl
    rw [hni] at hstep
    show some n'.id.id = g₁.map_parent
    rw [hni]
    exact h₁ n hn hstep
  · have hs2 : n'.id.id.step = g₂.current_step - 1 := by rw [← hstepeq]; exact hstep
    have hres := h₂ n' (List.mem_filter.mp hmem).1 hs2
    show some n'.id.id = g₁.map_parent
    rw [hmpeq]; exact hres

theorem TL_initSeed (d : NodeId) (title : String) (_hstep : d.step = 0) :
    TL (GPathM.initSeed d title) := by
  intro n hn _
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  rfl

-- ============================================================
-- Parents carry the map id `parent_id` names
-- ============================================================

def PMP (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, some p.id = n.id.parent_id

theorem PMP_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : PMP g) : PMP g' := by
  intro n' hn' p hp
  obtain ⟨n, hn, hid, _, hpar⟩ := hpr.nodes_derived n' hn'
  rw [hid]
  exact h n hn p (hpar p hp)

theorem PMP_addNode (g : GPathM) (d : NodeId) (title : String)
    (htl : TL g) (h : PMP g) : PMP (addNode g d title) := by
  intro n' hn' p hp
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_parents] at hp
    rw [← hEq, upMap_id]
    exact h n hn p hp
  · rcases List.mem_singleton.mp hmem with rfl
    have hpar : (addOwner (newPid g d) (upNode g d title)).parents = newParents g := rfl
    rw [hpar] at hp
    show some p.id = g.map_parent
    unfold newParents at hp
    split at hp
    · obtain ⟨m, hm, hmid⟩ := Parents.mem_nodes_of_mem_line g (g.current_step - 1) p hp
      rw [← hmid]
      exact htl m hm (by rw [hmid]; exact Parents.mem_line_step g (g.current_step - 1) p hp)
    · exact absurd hp List.not_mem_nil

theorem PMP_join (g₁ g₂ : GPathM) (h₁ : PMP g₁) (h₂ : PMP g₂) : PMP (join g₁ g₂) := by
  intro n' hn' p hp
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none =>
      rw [← hEq, hg] at hp ⊢
      exact h₁ n hn p hp
    | some m =>
      have hmid : m.id = n.id := node?_id_eq g₂ n.id m hg
      have hpar : (mergeNode n m).parents =
          n.parents ++ m.parents.filter (fun r => !n.parents.contains r) := rfl
      rw [← hEq, hg] at hp ⊢
      rw [hpar, List.mem_append] at hp
      show some p.id = (mergeNode n m).id.parent_id
      rcases hp with hp | hp
      · exact h₁ n hn p hp
      · have := h₂ m (List.mem_of_find?_eq_some hg) p (List.mem_filter.mp hp).1
        rw [hmid] at this; exact this
  · exact h₂ n' (List.mem_filter.mp hmem).1 p hp

theorem PMP_initSeed (d : NodeId) (title : String) : PMP (GPathM.initSeed d title) := by
  intro n hn p hp
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact absurd hp List.not_mem_nil

-- ============================================================
-- Both, over the machine
-- ============================================================

variable (reqOf : NodeId → List NodeId)

theorem TL_reachable (g : GPathM) (h : Reachable reqOf g) : TL g := by
  induction h with
  | seed d title hstep _ => exact TL_initSeed d title hstep
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show TL (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact TL_addNode _ d title (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr))
    · exact TL_of_pruned hpr ih
  | join g₁ g₂ hok _ _ ih₁ ih₂ => exact TL_join g₁ g₂ hok ih₁ ih₂

theorem PMP_reachable (g : GPathM) (h : Reachable reqOf g) : PMP g := by
  induction h with
  | seed d title _ _ => exact PMP_initSeed d title
  | up g d title _ _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show PMP (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact PMP_addNode _ d title (TL_of_pruned hpr (TL_reachable reqOf g hr))
        (PMP_of_pruned hpr ih)
    · exact PMP_of_pruned hpr ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact PMP_join g₁ g₂ ih₁ ih₂

theorem PMP_filterAll (g : GPathM) (reqs : List NodeId) (h : Reachable reqOf g) :
    PMP (filterAll g reqs) :=
  PMP_of_pruned (pruned_filterAll g reqs) (PMP_reachable reqOf g h)

-- ============================================================
-- The local condition, and what it forces
-- ============================================================

/-- **The local condition on `parent_id`.** `IsChain`'s parent link, read on
the ids: the node a chain picks at `k+1` records the map id it picked at `k`. -/
theorem parentId_coherent (h : GPathM) (hpmp : PMP h) (sel : Int → PathNodeId)
    (hchain : IsChain h sel) (k : Int) (hlo : 0 ≤ k) (hhi : k + 1 < h.current_step) :
    (sel (k + 1)).parent_id = some (sel k).id := by
  have hlink := hchain.2 k hlo hhi
  cases hn : h.node? (sel (k + 1)) with
  | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
  | some n =>
    rw [hn] at hlink
    have hnid : n.id = sel (k + 1) := node?_id_eq h _ n hn
    have := hpmp n (List.mem_of_find?_eq_some hn) (sel k) hlink
    rw [hnid] at this
    exact this.symm

theorem pathNodeId_ext {a b : PathNodeId} (h1 : a.id = b.id)
    (h2 : a.parent_id = b.parent_id) : a = b := by
  cases a with
  | mk ai ap =>
    cases b with
    | mk bi bp =>
      simp only at h1 h2
      rw [h1, h2]

/-- **A chain is determined by its map ids.** Two chains that agree on every
map id are the same chain. So at a pinned step there is no choice between two
path nodes: the pick is fixed by the requirement's map id and the map id below
it. -/
theorem chain_eq_of_mapIds_eq (h : GPathM) (hpmp : PMP h)
    (sel sel' : Int → PathNodeId)
    (hchain : IsChain h sel) (hchain' : IsChain h sel')
    (hroot : (sel 0).parent_id = none) (hroot' : (sel' 0).parent_id = none)
    (hids : ∀ k, 0 ≤ k → k < h.current_step → (sel k).id = (sel' k).id) :
    ∀ (m : Nat) (k : Int), k.toNat ≤ m → 0 ≤ k → k < h.current_step → sel k = sel' k := by
  intro m
  induction m with
  | zero =>
    intro k hm hlo hhi
    have hk : k = 0 := by omega
    subst hk
    exact pathNodeId_ext (hids 0 (Int.le_refl _) hhi) (by rw [hroot, hroot'])
  | succ m ih =>
    intro k hm hlo hhi
    if hz : k = 0 then
      subst hz
      exact pathNodeId_ext (hids 0 (Int.le_refl _) hhi) (by rw [hroot, hroot'])
    else
      have hprev : sel (k - 1) = sel' (k - 1) :=
        ih (k - 1) (by omega) (by omega) (by omega)
      have hp : (sel k).parent_id = some (sel (k - 1)).id := by
        have := parentId_coherent h hpmp sel hchain (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega] at this
        exact this
      have hp' : (sel' k).parent_id = some (sel' (k - 1)).id := by
        have := parentId_coherent h hpmp sel' hchain' (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega] at this
        exact this
      exact pathNodeId_ext (hids k hlo hhi) (by rw [hp, hp', hprev])

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ParentId.PMP_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PMP_reachable

/-- info: 'AbsSat.GraphPath.Model.ParentId.chain_eq_of_mapIds_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_eq_of_mapIds_eq

end AbsSat.GraphPath.Model.ParentId
