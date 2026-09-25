-- lean/improves_bin/AbsSatBin/GraphPath/Model/MapReachable.lean
import AbsSatBin.GraphPath.Model.OwnersInvariants
import AbsSatBin.GraphPath.Model.GownersNodes
import AbsSatBin.GraphPath.Model.L6
import AbsSatBin.GraphMap.CnfMapBin

/-!
# The machine run by the bin map of `φ` — **rewritten** (`lean_project`'s `MapReachable`)

`Reachable reqOf forb` is parametric in the map. `MapReachable φ` is the run the machine actually
does over the bin map of `φ`: requirements `CnfMapBin.reqOf φ`, prohibited windows
`CnfMapBin.isProhibited φ`, and every node it visits a node of the map.

Two invariants are read off it:

* `NodesOnMap` (as in `lean_project`): every node of the graph is a node the map builds;
* **`NoForb`** (new): no node of the graph carries a prohibited identifier. The UP never creates
  one (`not_forb_of_mem_newRowIds`), pruning only removes nodes, and join only brings nodes of
  another run. This is what the decode reads at the third literal of a clause, in place of the
  classic "row `000` is not on the map".
-/

namespace AbsSatBin.GraphPath.Model.MapReachable

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM

variable (φ : Cnf)

-- ============================================================
-- Nodes on the map
-- ============================================================

/-- Every node of the graph is a node the map of `φ` builds. -/
def NodesOnMap (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, n.id.id ∈ mapNodes φ n.id.id.step

theorem NodesOnMap_of_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : NodesOnMap φ g) : NodesOnMap φ g' := by
  intro n hn
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n hn
  rw [hid]
  exact h m hm

theorem NodesOnMap_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d ∈ mapNodes φ d.step) (h : NodesOnMap φ g) :
    NodesOnMap φ (addNode g d title forb) := by
  intro n hn
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by rw [← hEq]; exact upMap_id g d forb m
    rw [hid]
    exact h m hm
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb n).mp hmem
    rw [show (rowNode g d title pid).id.id = d from mapId_of_mem_newRowIds g d forb pid hpid]
    exact hd

theorem NodesOnMap_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) (hd : d ∈ mapNodes φ d.step) (h : NodesOnMap φ g) :
    NodesOnMap φ (upFiltering g reqs d title forb) := by
  have hf := NodesOnMap_of_pruned φ (pruned_filterAll g reqs) h
  have hadd := NodesOnMap_addNode φ _ d title forb hd hf
  simp only [upFiltering, up]
  split
  · split
    · exact NodesOnMap_of_pruned φ (pruned_review _) hadd
    · exact hadd
  · exact hf

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
-- No prohibited identifier (new)
-- ============================================================

/-- No node of the graph carries an identifier `forb` prohibits. -/
def NoForb (forb : PathNodeId → Bool) (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, forb n.id = false

theorem NoForb_of_pruned (forb : PathNodeId → Bool) {g g' : GPathM} (hpr : Pruned g g')
    (h : NoForb forb g) : NoForb forb g' := by
  intro n hn
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n hn
  rw [hid]
  exact h m hm

/-- **The UP never creates a prohibited node** — the old nodes keep their identifiers, and the
row is `newRowIds`, which leaves the prohibited ones out. -/
theorem NoForb_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (h : NoForb forb g) : NoForb forb (addNode g d title forb) := by
  intro n hn
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by rw [← hEq]; exact upMap_id g d forb m
    rw [hid]
    exact h m hm
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb n).mp hmem
    rw [rowNode_id]
    exact not_forb_of_mem_newRowIds g d forb pid hpid

theorem NoForb_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) (h : NoForb forb g) :
    NoForb forb (upFiltering g reqs d title forb) := by
  have hf := NoForb_of_pruned forb (pruned_filterAll g reqs) h
  have hadd := NoForb_addNode _ d title forb hf
  simp only [upFiltering, up]
  split
  · split
    · exact NoForb_of_pruned forb (pruned_review _) hadd
    · exact hadd
  · exact hf

theorem NoForb_join (forb : PathNodeId → Bool) (g₁ g₂ : GPathM) (h₁ : NoForb forb g₁)
    (h₂ : NoForb forb g₂) : NoForb forb (join g₁ g₂) := by
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

/-- A root identifier (no parent) is never prohibited: the window needs two parents. -/
theorem isProhibited_root (d : NodeId) :
    isProhibited φ { id := d, parent_id := none } = false := by
  simp [isProhibited]

theorem NoForb_initSeed (d : NodeId) (title : String) :
    NoForb (isProhibited φ) (GPathM.initSeed d title) := by
  intro n hn
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact isProhibited_root φ d

-- ============================================================
-- The machine run *by the bin map of φ*
-- ============================================================

/-- The run over the bin map of `φ`: its requirements, its prohibited windows, and every node it
visits a node of the map. -/
inductive MapReachable : GPathM → Prop where
  | seed (d : NodeId) (title : String) (hstep : d.step = 0)
      (hmem : d ∈ mapNodes φ d.step) :
      MapReachable (GPathM.initSeed d title)
  | up (g : GPathM) (d : NodeId) (title : String)
      (hstep : d.step = g.current_step) (hmem : d ∈ mapNodes φ d.step) :
      MapReachable g → MapReachable (GPathM.upFiltering g (reqOf φ d) d title (isProhibited φ))
  | join (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂) :
      MapReachable g₁ → MapReachable g₂ → MapReachable (GPathM.join g₁ g₂)

/-- **The projection.** Everything proved about `Reachable` applies to a `MapReachable` run:
`reqOf_backward` and `reqOf_functional` pay `up`'s two side conditions. Only `Bounded` is
needed — the bin map has at most one requirement per node. -/
theorem reachable_of_mapReachable (hb : Bounded φ) (g : GPathM) (h : MapReachable φ g) :
    Reachable (reqOf φ) (isProhibited φ) g := by
  induction h with
  | seed d title hstep _ =>
    exact Reachable.seed d title hstep (fun req hreq => reqOf_backward φ hb d req hreq)
  | up g d title hstep _ _ ih =>
    exact Reachable.up g d title hstep
      (fun req hreq => reqOf_backward φ hb d req hreq)
      (fun r₁ r₂ h₁ h₂ _ => reqOf_functional φ d r₁ h₁ r₂ h₂) ih
  | join g₁ g₂ hok _ _ ih₁ ih₂ => exact Reachable.join g₁ g₂ hok ih₁ ih₂

theorem nodesOnMap_of_mapReachable (g : GPathM) (h : MapReachable φ g) : NodesOnMap φ g := by
  induction h with
  | seed d title _ hmem => exact NodesOnMap_initSeed φ d title hmem
  | up g d title _ hmem _ ih => exact NodesOnMap_upFiltering φ g _ d title _ hmem ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact NodesOnMap_join φ g₁ g₂ ih₁ ih₂

theorem noForb_of_mapReachable (g : GPathM) (h : MapReachable φ g) :
    NoForb (isProhibited φ) g := by
  induction h with
  | seed d title _ _ => exact NoForb_initSeed φ d title
  | up g d title _ _ _ ih => exact NoForb_upFiltering g _ d title _ ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact NoForb_join _ g₁ g₂ ih₁ ih₂

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

/-- **No chain pick is prohibited.** -/
theorem chain_not_forb (forb : PathNodeId → Bool) (g : GPathM) (h : NoForb forb g)
    (sel : Int → PathNodeId) (hchain : IsChain g sel) (k : Int) (hlo : 0 ≤ k)
    (hhi : k < g.current_step) : forb (sel k) = false := by
  obtain ⟨hsome, _⟩ := hchain.1 k hlo hhi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hnid : n.id = sel k := node?_id_eq g _ n hn
  rw [← hnid]
  exact h n (List.mem_of_find?_eq_some hn)

/-- info: 'AbsSatBin.GraphPath.Model.MapReachable.reachable_of_mapReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reachable_of_mapReachable

/-- info: 'AbsSatBin.GraphPath.Model.MapReachable.noForb_of_mapReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noForb_of_mapReachable

end AbsSatBin.GraphPath.Model.MapReachable
