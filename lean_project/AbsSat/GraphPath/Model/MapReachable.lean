-- lean_project/AbsSat/GraphPath/Model/MapReachable.lean
import AbsSat.GraphPath.Model.OwnersInvariants
import AbsSat.GraphPath.Model.GownersNodes
import AbsSat.GraphPath.Model.L6
import AbsSat.GraphMap.CnfMap

/-!
# The machine, run by the map of a formula

`Reachable` is parametric in `reqOf` and places **no constraint on which
`NodeId`s appear in the graph**: its `up` constructor takes an arbitrary `d`
and asks only that `d.step = g.current_step` and that `reqOf d` points
backwards and is functional.

For the decode direction that is not enough, and the gap is not academic. At a
clause step the map builds seven nodes, indices `1..7` — the seven satisfying
rows of a 3-OR. `reqOfCnf` is deliberately uniform there and answers for index
`0` too, with exactly the requirements of the row the map omits: *all three
literals false*. A chain standing on such a node would satisfy its
requirements and the decode argument would conclude the clause is **violated**.
So without the invariant below, the theorem this module supports is false, not
merely unproved.

`MapReachable φ` is `Reachable (reqOfCnf φ)` with the missing side condition
put back: every node added comes from the map. It projects onto `Reachable`
(so everything already proved applies) and yields `NodesOnMap`.

`NodesOnMap` is much cheaper than `GownersNodes.GN`, which needed a lemma per
operation: it is stable under *any* narrowing, so the whole review — every
filter, every sweep, every removal — collapses into one `Pruned` lemma.
-/

namespace AbsSat.GraphPath.Model.MapReachable

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

variable (φ : Cnf)

/-- Every node of the graph is a node the map of `φ` builds. -/
def NodesOnMap (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, n.id.id ∈ mapNodes φ n.id.id.step

-- ============================================================
-- Narrowing preserves it — one lemma for the whole review
-- ============================================================

theorem NodesOnMap_of_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : NodesOnMap φ g) : NodesOnMap φ g' := by
  intro n hn
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n hn
  rw [hid]
  exact h m hm

theorem NodesOnMap_filterAll (g : GPathM) (reqs : List NodeId) (h : NodesOnMap φ g) :
    NodesOnMap φ (filterAll g reqs) :=
  NodesOnMap_of_pruned φ (pruned_filterAll g reqs) h

-- ============================================================
-- Growth
-- ============================================================

theorem NodesOnMap_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d ∈ mapNodes φ d.step) (h : NodesOnMap φ g) :
    NodesOnMap φ (addNode g d title) := by
  intro n hn
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by rw [← hEq]; exact upMap_id g d m
    rw [hid]
    exact h m hm
  · rcases List.mem_singleton.mp hmem with rfl
    have hid : (addOwner (newPid g d) (upNode g d title)).id.id = d := rfl
    rw [hid]
    exact hd

theorem NodesOnMap_up (g : GPathM) (d : NodeId) (title : String)
    (hd : d ∈ mapNodes φ d.step) (h : NodesOnMap φ g) :
    NodesOnMap φ (up g d title) := by
  simp only [GPathM.up]
  split
  · exact NodesOnMap_addNode φ g d title hd h
  · exact h

theorem NodesOnMap_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId)
    (title : String) (hd : d ∈ mapNodes φ d.step) (h : NodesOnMap φ g) :
    NodesOnMap φ (upFiltering g reqs d title) :=
  NodesOnMap_up φ _ d title hd (NodesOnMap_filterAll φ g reqs h)

theorem NodesOnMap_join (g₁ g₂ : GPathM) (h₁ : NodesOnMap φ g₁) (h₂ : NodesOnMap φ g₂) :
    NodesOnMap φ (join g₁ g₂) := by
  intro n hn
  rw [GownersNodes.join_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by
      rw [← hEq]
      cases g₂.node? m.id with
      | some q => rfl
      | none => rfl
    rw [hid]
    exact h₁ m hm
  · exact h₂ n (List.mem_filter.mp hmem).1

theorem NodesOnMap_initSeed (d : NodeId) (title : String)
    (hd : d ∈ mapNodes φ d.step) : NodesOnMap φ (GPathM.initSeed d title) := by
  intro n hn
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact hd

-- ============================================================
-- The machine run *by the map of φ*
-- ============================================================

/-- `Reachable (reqOfCnf φ)` with the side condition `Reachable` is missing:
every node the run introduces is a node of the map. -/
inductive MapReachable : GPathM → Prop where
  | seed (d : NodeId) (title : String) (hstep : d.step = 0)
      (hmem : d ∈ mapNodes φ d.step) :
      MapReachable (GPathM.initSeed d title)
  | up (g : GPathM) (d : NodeId) (title : String)
      (hstep : d.step = g.current_step) (hmem : d ∈ mapNodes φ d.step) :
      MapReachable g → MapReachable (GPathM.upFiltering g (reqOfCnf φ d) d title)
  | join (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂) :
      MapReachable g₁ → MapReachable g₂ → MapReachable (GPathM.join g₁ g₂)

/-- **The projection.** Everything already proved about `Reachable` — L1,
`L1_cor`, the shape invariants, the chain results — applies to a
`MapReachable` run, because `reqOfCnf_backward` and `reqOfCnf_functional` pay
`up`'s two side conditions once and for all. -/
theorem reachable_of_mapReachable (hwf : WF φ) (g : GPathM) (h : MapReachable φ g) :
    Reachable (reqOfCnf φ) g := by
  induction h with
  | seed d title hstep _ =>
    exact Reachable.seed d title hstep (fun req hreq =>
      reqOfCnf_backward φ hwf d req hreq)
  | up g d title hstep _ _ ih =>
    exact Reachable.up g d title hstep
      (fun req hreq => by
        have := reqOfCnf_backward φ hwf d req hreq
        omega)
      (fun r₁ r₂ h₁ h₂ hs => reqOfCnf_functional φ hwf d r₁ h₁ r₂ h₂ hs) ih
  | join g₁ g₂ hok _ _ ih₁ ih₂ => exact Reachable.join g₁ g₂ hok ih₁ ih₂

theorem nodesOnMap_of_mapReachable (g : GPathM) (h : MapReachable φ g) :
    NodesOnMap φ g := by
  induction h with
  | seed d title _ hmem => exact NodesOnMap_initSeed φ d title hmem
  | up g d title _ hmem _ ih => exact NodesOnMap_upFiltering φ g _ d title hmem ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact NodesOnMap_join φ g₁ g₂ ih₁ ih₂

-- ============================================================
-- Read along a chain
-- ============================================================

/-- The invariant as the decode direction consumes it. -/
def ChainOnMap (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → (sel k).id ∈ mapNodes φ k

theorem chainOnMap_of_nodesOnMap (g : GPathM) (h : NodesOnMap φ g)
    (sel : Int → PathNodeId) (hchain : IsChain g sel) : ChainOnMap φ g sel := by
  intro k hlo hhi
  obtain ⟨hsome, hstep⟩ := hchain.1 k hlo hhi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hnid : n.id = sel k := node?_id_eq g _ n hn
  have := h n (List.mem_of_find?_eq_some hn)
  rw [hnid, hstep] at this
  exact this

/-- info: 'AbsSat.GraphPath.Model.MapReachable.reachable_of_mapReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reachable_of_mapReachable

/-- info: 'AbsSat.GraphPath.Model.MapReachable.nodesOnMap_of_mapReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nodesOnMap_of_mapReachable

end AbsSat.GraphPath.Model.MapReachable
