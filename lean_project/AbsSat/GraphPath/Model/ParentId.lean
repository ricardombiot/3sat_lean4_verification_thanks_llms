-- lean_project/AbsSat/GraphPath/Model/ParentId.lean
import AbsSat.GraphPath.Model.MapChain

/-!
**The local condition on `parent_id` — and a chain is determined by its map
ids.**

v33 sized the residual gap in `ReqSatImpliesOwned`: at a pinned step the owner
set holds at most two path nodes, both carrying the map id the requirement
names, differing only in `parent_id`. So the question is which parent.

`parent_id` is not decoration. `addNode` builds `⟨d, g.map_parent, none⟩`, where
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

/-- **A candidate parent of the row carries the state's map parent.** The move that turns a row
node's recorded parent back into the key of the side it came from; `TL` is what makes it work. -/
theorem mapId_of_mem_newParents (g : GPathM) (hpos : 0 < g.current_step) (htl : TL g)
    (q : PathNodeId) (h : q ∈ newParents g) : some q.id = g.map_parent := by
  unfold newParents at h
  rw [if_pos hpos] at h
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
  exact htl n (List.mem_filter.mp hn).1 (eq_of_beq (List.mem_filter.mp hn).2)

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
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title n').mp hmem
    rw [rowNode_id, mapId_of_mem_newRowIds g d pid hpid]
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

/-- **GPMP** — *the grandparent the id declares is the parent of every parent.*

The sibling of `PMP` one level up, and the whole point of widening the window:
where `PMP` reads `IsChain`'s parent link off the ids, `GPMP` reads the
*grandparent* link off them too. It holds by construction of the windowed `UP`
(`shiftPid` copies `last.parent_id` into the new id's `gparent_id`, and every
node of a row is grouped by an identifier that already contains it), so all the
nodes merged into one row node agree on it.

Note it needs no `m ∈ h.nodes` side condition: `p` is a `PathNodeId` and
carries its own `parent_id`. -/
def GPMP (h : GPathM) : Prop :=
  (∀ n ∈ h.nodes, ∀ p ∈ n.parents, n.id.gparent_id = p.parent_id) ∧
  (∀ n ∈ h.nodes, n.id.parent_id = none → n.id.gparent_id = none)

theorem GPMP_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : GPMP g) : GPMP g' := by
  refine ⟨?_, ?_⟩
  · intro n' hn' p hp
    obtain ⟨n, hn, hid, _, hpar⟩ := hpr.nodes_derived n' hn'
    rw [hid]
    exact h.1 n hn p (hpar p hp)
  · intro n' hn' hr
    obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
    rw [hid] at hr ⊢
    exact h.2 n hn hr

theorem PMP_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : PMP g) : PMP g' := by
  intro n' hn' p hp
  obtain ⟨n, hn, hid, _, hpar⟩ := hpr.nodes_derived n' hn'
  rw [hid]
  exact h n hn p (hpar p hp)

/-- **`PMP` survives the row, and for free.** With a single new node this needed
`TL` — that the whole top line carried `map_parent`. With the row it is immediate:
the parents of a row node are precisely the last-row nodes that *shift* to its
identifier, and the shift writes their map id into `parent_id`. The `TL`
hypothesis is kept only so callers do not have to change. -/
theorem PMP_addNode (g : GPathM) (d : NodeId) (title : String)
    (_htl : TL g) (h : PMP g) : PMP (addNode g d title) := by
  intro n' hn' p hp
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_parents] at hp
    rw [← hEq, upMap_id]
    exact h n hn p hp
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title n').mp hmem
    rw [rowNode_parents] at hp
    rw [rowNode_id, ← shiftPid_of_mem_rowParents g d pid p hp]
    rfl

/-- **`GPMP` holds by construction of the row.** `shiftPid` copies the parent's
own `parent_id` into the new identifier's `gparent_id`, and a row node's parents
are exactly the last-row nodes that shift to it — so they all agree on it. This
is the level of history the window buys, and it costs one line. -/
theorem GPMP_addNode (g : GPathM) (d : NodeId) (title : String)
    (h : GPMP g) : GPMP (addNode g d title) := by
  refine ⟨?_, ?_⟩
  · intro n' hn' p hp
    rw [addNode_nodes] at hn'
    rcases List.mem_append.mp hn' with hmem | hmem
    · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
      rw [← hEq, upMap_parents] at hp
      rw [← hEq, upMap_id]
      exact h.1 n hn p hp
    · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title n').mp hmem
      rw [rowNode_parents] at hp
      rw [rowNode_id, ← shiftPid_of_mem_rowParents g d pid p hp]
      rfl
  · intro n' hn' hr
    rw [addNode_nodes] at hn'
    rcases List.mem_append.mp hn' with hmem | hmem
    · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
      rw [← hEq, upMap_id] at hr ⊢
      exact h.2 n hn hr
    · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title n').mp hmem
      rw [rowNode_id] at hr ⊢
      by_cases hpos : 0 < g.current_step
      · exact absurd hr (parent_id_ne_none_of_mem_newRowIds g d pid hpos hpid)
      · rw [newRowIds_of_zero g d hpos] at hpid
        rcases List.mem_singleton.mp hpid with rfl
        rfl

theorem GPMP_join (g₁ g₂ : GPathM) (h₁ : GPMP g₁) (h₂ : GPMP g₂) : GPMP (join g₁ g₂) := by
  have hroot : ∀ n' ∈ (join g₁ g₂).nodes, n'.id.parent_id = none → n'.id.gparent_id = none := by
    intro n' hn' hr
    rw [GownersNodes.join_nodes] at hn'
    rcases List.mem_append.mp hn' with hmem | hmem
    · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
      cases hg : g₂.node? n.id with
      | none => rw [← hEq, hg] at hr ⊢; exact h₁.2 n hn hr
      | some m =>
        rw [← hEq, hg] at hr ⊢
        exact h₁.2 n hn hr
    · exact h₂.2 n' (List.mem_filter.mp hmem).1 hr
  refine ⟨?_, hroot⟩
  intro n' hn' p hp
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none =>
      rw [← hEq, hg] at hp ⊢
      exact h₁.1 n hn p hp
    | some m =>
      have hmid : m.id = n.id := node?_id_eq g₂ n.id m hg
      have hpar : (mergeNode n m).parents =
          n.parents ++ m.parents.filter (fun r => !n.parents.contains r) := rfl
      rw [← hEq, hg] at hp ⊢
      rw [hpar, List.mem_append] at hp
      show (mergeNode n m).id.gparent_id = p.parent_id
      rcases hp with hp | hp
      · exact h₁.1 n hn p hp
      · have := h₂.1 m (List.mem_of_find?_eq_some hg) p (List.mem_filter.mp hp).1
        rw [hmid] at this; exact this
  · exact h₂.1 n' (List.mem_filter.mp hmem).1 p hp

theorem GPMP_initSeed (d : NodeId) (title : String) : GPMP (GPathM.initSeed d title) := by
  refine ⟨?_, ?_⟩
  · intro n hn p hp
    rw [initSeed_nodes] at hn
    rcases List.mem_singleton.mp hn with rfl
    exact absurd hp List.not_mem_nil
  · intro n hn _
    rw [initSeed_nodes] at hn
    rcases List.mem_singleton.mp hn with rfl
    rfl

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

theorem GPMP_reachable (g : GPathM) (h : Reachable reqOf g) : GPMP g := by
  induction h with
  | seed d title _ _ => exact GPMP_initSeed d title
  | up g d title _ _ _ _ ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show GPMP (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact GPMP_addNode _ d title (GPMP_of_pruned hpr ih)
    · exact GPMP_of_pruned hpr ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact GPMP_join g₁ g₂ ih₁ ih₂

theorem GPMP_filterAll (g : GPathM) (reqs : List NodeId) (h : Reachable reqOf g) :
    GPMP (filterAll g reqs) :=
  GPMP_of_pruned (pruned_filterAll g reqs) (GPMP_reachable reqOf g h)

/-- info: 'AbsSat.GraphPath.Model.ParentId.GPMP_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GPMP_reachable

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

/-- **The local condition on `gparent_id`.** The node a chain picks at `k+1`
records, in its third component, the *`parent_id`* of the node it picked at `k`
— so the pick at `k+1` already names the map id of the pick at `k-1`. This is
what makes a pair of adjacent picks carry three steps of history. -/
theorem gparentId_coherent (h : GPathM) (hgpmp : GPMP h) (sel : Int → PathNodeId)
    (hchain : IsChain h sel) (k : Int) (hlo : 0 ≤ k) (hhi : k + 1 < h.current_step) :
    (sel (k + 1)).gparent_id = (sel k).parent_id := by
  have hlink := hchain.2 k hlo hhi
  cases hn : h.node? (sel (k + 1)) with
  | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
  | some n =>
    rw [hn] at hlink
    have hnid : n.id = sel (k + 1) := node?_id_eq h _ n hn
    have := hgpmp.1 n (List.mem_of_find?_eq_some hn) (sel k) hlink
    rw [hnid] at this
    exact this

theorem pathNodeId_ext {a b : PathNodeId} (h1 : a.id = b.id)
    (h2 : a.parent_id = b.parent_id) (h3 : a.gparent_id = b.gparent_id) : a = b := by
  cases a with
  | mk ai ap ag =>
    cases b with
    | mk bi bp bg =>
      simp only at h1 h2 h3
      rw [h1, h2, h3]

/-- **A chain is determined by its map ids.** Two chains that agree on every
map id are the same chain. So at a pinned step there is no choice between two
path nodes: the pick is fixed by the requirement's map id and the map id below
it. -/
theorem chain_eq_of_mapIds_eq (h : GPathM) (hpmp : PMP h) (hgpmp : GPMP h)
    (sel sel' : Int → PathNodeId)
    (hchain : IsChain h sel) (hchain' : IsChain h sel')
    (hroot : (sel 0).parent_id = none) (hroot' : (sel' 0).parent_id = none)
    (hrootg : (sel 0).gparent_id = none) (hrootg' : (sel' 0).gparent_id = none)
    (hids : ∀ k, 0 ≤ k → k < h.current_step → (sel k).id = (sel' k).id) :
    ∀ (m : Nat) (k : Int), k.toNat ≤ m → 0 ≤ k → k < h.current_step → sel k = sel' k := by
  intro m
  induction m with
  | zero =>
    intro k hm hlo hhi
    have hk : k = 0 := by omega
    subst hk
    exact pathNodeId_ext (hids 0 (Int.le_refl _) hhi) (by rw [hroot, hroot'])
      (by rw [hrootg, hrootg'])
  | succ m ih =>
    intro k hm hlo hhi
    if hz : k = 0 then
      subst hz
      exact pathNodeId_ext (hids 0 (Int.le_refl _) hhi) (by rw [hroot, hroot'])
        (by rw [hrootg, hrootg'])
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
      have hg : (sel k).gparent_id = (sel (k - 1)).parent_id := by
        have := gparentId_coherent h hgpmp sel hchain (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega] at this
        exact this
      have hg' : (sel' k).gparent_id = (sel' (k - 1)).parent_id := by
        have := gparentId_coherent h hgpmp sel' hchain' (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega] at this
        exact this
      exact pathNodeId_ext (hids k hlo hhi) (by rw [hp, hp', hprev]) (by rw [hg, hg', hprev])

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ParentId.PMP_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PMP_reachable

/-- info: 'AbsSat.GraphPath.Model.ParentId.chain_eq_of_mapIds_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_eq_of_mapIds_eq

-- ============================================================
-- The pinned half of `ReqSatImpliesOwned`, reduced to one existence
-- ============================================================

/-!
Putting `MapChain.owner_at_req_shares_mapid` (the map id of every owner at a
pinned step agrees with the chain's pick) together with `parentId_coherent`
(the chain's pick has a determined `parent_id`) settles which owner is the
chain's: the one whose `parent_id` agrees. A `PathNodeId` is nothing but those
two fields.

So the pinned half of `ReqSatImpliesOwned` reduces to a single **existence**:
that some owner at the required step carries the chain's `parent_id`.

**Measured** (`lake exe extend --randompinnedchain`, two seeds, 160 instances):
over **4,429,212** (chain node, requirement) pairs, **exactly one** owner
matches the chain's predecessor — never zero, never two — and the chain's pick
is a member of the owner set in every single case.

**And it corrects a tempting overshoot.** The obligation is *membership*, not
"every owner at a pinned step equals the chain's pick": 277,070 of those pairs
(23.4%, 1,035,280 of them) have an owner set of width two, so the stronger
reading is false on chain nodes, not merely unproven.
-/

/-- **Which owner is the chain's.** An owner at a pinned step that carries the
chain's `parent_id` *is* the chain's pick — its map id already agrees. -/
theorem owner_eq_chain_pick (reqOf : NodeId → List NodeId) (g : GPathM)
    (hrf : ReqFiltered reqOf g) (sel : Int → PathNodeId)
    (hrs : MapChain.ReqSatisfying reqOf g sel)
    (j : Int) (hjlo : 0 ≤ j) (hjhi : j < g.current_step)
    (n : PNodeM) (hn : g.node? (sel j) = some n)
    (req : NodeId) (hreq : req ∈ reqOf (sel j).id)
    (hrlo : 0 ≤ req.step) (hrhi : req.step < g.current_step)
    (q : PathNodeId) (hq : q ∈ ownersAt n.owners req.step)
    (hpar : q.parent_id = (sel req.step).parent_id)
    (hgpar : q.gparent_id = (sel req.step).gparent_id) :
    q = sel req.step :=
  pathNodeId_ext
    (MapChain.owner_at_req_shares_mapid reqOf g hrf sel hrs j hjlo hjhi n hn req hreq
      hrlo hrhi q hq)
    hpar hgpar

/-- **The single remaining obligation of the pinned half.** Some owner at the
required step carries the chain's **window** — `parent_id` and, since the window
widened, `gparent_id` as well. Measured at exactly one for the `parent_id` half,
over 4,429,212 (chain node, requirement) pairs across two seeds; not proved.
The `gparent_id` conjunct is a strictly stronger demand on the owner list and
has not been measured. -/
def OwnerMatchesPredecessor (reqOf : NodeId → List NodeId) (g : GPathM)
    (sel : Int → PathNodeId) : Prop :=
  ∀ j, 0 ≤ j → j < g.current_step → ∀ n, g.node? (sel j) = some n →
    ∀ req ∈ reqOf (sel j).id, 0 ≤ req.step → req.step < g.current_step →
      ∃ q ∈ ownersAt n.owners req.step,
        q.parent_id = (sel req.step).parent_id ∧ q.gparent_id = (sel req.step).gparent_id

/-- **And it gives the pinned half.** Existence of a matching owner plus the
two proved facts puts the chain's own pick in the owner set. -/
theorem chain_pick_mem_owners (reqOf : NodeId → List NodeId) (g : GPathM)
    (hrf : ReqFiltered reqOf g) (sel : Int → PathNodeId)
    (hrs : MapChain.ReqSatisfying reqOf g sel)
    (hmatch : OwnerMatchesPredecessor reqOf g sel)
    (j : Int) (hjlo : 0 ≤ j) (hjhi : j < g.current_step)
    (n : PNodeM) (hn : g.node? (sel j) = some n)
    (req : NodeId) (hreq : req ∈ reqOf (sel j).id)
    (hrlo : 0 ≤ req.step) (hrhi : req.step < g.current_step) :
    sel req.step ∈ ownersAt n.owners req.step := by
  obtain ⟨q, hq, hpar, hgpar⟩ := hmatch j hjlo hjhi n hn req hreq hrlo hrhi
  have : q = sel req.step :=
    owner_eq_chain_pick reqOf g hrf sel hrs j hjlo hjhi n hn req hreq hrlo hrhi q hq hpar hgpar
  rw [← this]; exact hq

/-- info: 'AbsSat.GraphPath.Model.ParentId.chain_pick_mem_owners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_pick_mem_owners

-- ============================================================
-- The bridge between the two ledgers: refuted in general,
-- true exactly where it is needed
-- ============================================================

/-!
`OwnerMatchesPredecessor` needs a specific path node to be *in* an owner list.
The owners ledger is built by `addNode` and pruned by `intersectOwners` against
`unionOwnersOf`; the parents ledger is built by `newParents`. The minimal
candidate bridge is that they agree on the direct links.

**It is false.** `lake exe extend --randombridge`, 60 instances, 282,077 nodes:
**37** parent links and **71** son links out of 328,086 are missing from the
owners. Small — 0.011% — but not zero, and enough to sink any attempt to prove
`ParentIsOwner`.

The reason is visible in the code: **ownership pruning never unlinks a
parent.** `removeNode` unlinks, but `intersectOwners` only shrinks `owners`, so
a node can keep a structural predecessor that propagation has already ruled
out. The parents table is the stale one.

**And it is true exactly where the obligation needs it.** Restricted to the
consecutive picks of requirement-satisfying chains
(`lake exe extend --stale`, two seeds): **3,556,470 pairs, zero** where the
parent is not an owner. The 313 nodes holding a stale parent are off every such
chain — and the stale links *scale* with campaign size (36 → 277) while the
chain exceptions never appear at all.

**A caveat this puts on `PathExists.exists_isChain`.** That descent picks an
*arbitrary* parent at each step, and stale parent links exist — so the path it
builds really can use one. v27 said the path need not be co-owned; this says
the gap is not merely theoretical.
-/

/-- Every parent of a node is one of its owners. ⚠ **Refuted** — 37 of 328,086
parent links are missing from the owners. Kept as the record of the minimal
bridge that does not hold, and of why: ownership pruning never unlinks a
parent. -/
def ParentIsOwner (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, p ∈ n.owners

/-- The same for sons. ⚠ **Refuted** — 71 of 328,086. -/
def SonIsOwner (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ s ∈ n.sons, s ∈ n.owners

/-- **The bridge that survives**: the parent link between consecutive picks of
a requirement-satisfying chain is an ownership link. Measured at 992,719 pairs
with no exception; not proved. It is `OwnerMatchesPredecessor` for the case
`req.step = j - 1`, and the general case is the same statement further down. -/
def ChainParentIsOwner (reqOf : NodeId → List NodeId) (g : GPathM)
    (sel : Int → PathNodeId) : Prop :=
  MapChain.ReqSatisfying reqOf g sel →
    ∀ k, 0 ≤ k → k + 1 < g.current_step →
      ∀ n, g.node? (sel (k + 1)) = some n → sel k ∈ n.owners

end AbsSat.GraphPath.Model.ParentId
