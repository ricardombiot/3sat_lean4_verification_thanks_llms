-- lean/improves_bin/AbsSatBin/GraphPath/Model/UpBin.lean
import AbsSatBin.GraphPath.Model.GPathM

/-!
# The UP with prohibited windows

Mirror of `julia/improves_bin/src/graph_path/graph_path_up.jl` (commits `92315b1`, `ba6cc6d`,
`5697d96`). The classic `GPathM.addNode` adds one node per identifier the window shift gives
to the last row. The bin UP adds the same row **minus the prohibited identifiers**:

* `group_parents_by_shifted_id` skips every `path_id_node ∈ prohibited` → `rowIdsW` filters
  `newRowIds` by `!forb`. Only the list of row identifiers changes: a row node's parents and
  owners (`rowParents`, `rowOwners`) depend on its own identifier, not on which other
  identifiers exist, so they are reused as they are.
* `add_row!` marks the gpath invalid when nothing is left → nothing to do here. `GPathM`'s
  validity is *derived* (every step below `current_step` has a global owner), so a row with no
  node leaves the new step without owners and the state is invalid by itself
  (`isValid_addNodeW_of_nil`). Julia also leaves the step un-advanced; nothing reads the step of
  an invalid gpath, which `send_to_destine!` drops.
* skipping a window sets `review_owners = true`, and `do_up!` then runs `make_review_owners!`
  after advancing the step → `upW` runs `review` **only when a window was skipped**
  (`skipsWindow`). With the flag down Julia does not review, so neither does this.

The prohibition is a parameter `forb : PathNodeId → Bool` rather than the map, so this module
does not depend on the map at all. The machine passes `CnfMapBin.isProhibited φ`.

**Where the indices matter.** A prohibited window is `(L3=0, L2=0, L1=0)`, most recent first,
and it is recognised on the *shifted* identifier: `shiftPid last d` is
`(d, last.id, last.parent_id)`, so it can only match when `d` is the `L3` node and the parent of
the row node stands at `L2` with *its* parent at `L1`. That needs the window of three
(`gparent_id := last.parent_id`), which `GPathM.shiftPid` always builds. Checked by `run_tests`.
-/

namespace AbsSatBin.GraphPath.Model

open AbsSatBin.Utils.Alias

namespace GPathM

-- ============================================================
-- The row, minus the prohibited identifiers
-- ============================================================

/-- The identifiers of the row the bin UP adds. -/
def rowIdsW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) : List PathNodeId :=
  (newRowIds g d).filter (fun pid => !forb pid)

/-- Some candidate identifier of the row was prohibited: Julia's `review_owners = true`. -/
def skipsWindow (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) : Bool :=
  (newRowIds g d).any forb

def gainedSonsW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) (n : PNodeM) :
    List PathNodeId :=
  (rowIdsW g d forb).filter (fun pid => (rowParents g d pid).contains n.id)

def gainedOwnersW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) (n : PNodeM) :
    List PathNodeId :=
  (rowIdsW g d forb).filter (fun pid => (rowOwners g d pid).contains n.id)

/-- What `addNodeW` does to every pre-existing node. -/
def upMapW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) (n : PNodeM) : PNodeM :=
  { n with sons := n.sons ++ gainedSonsW g d forb n,
           owners := n.owners ++ gainedOwnersW g d forb n }

def newRowW (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    List PNodeM :=
  (rowIdsW g d forb).map (rowNode g d title)

/-- **The bin `add_row!`**: `addNode` over the row without its prohibited identifiers. -/
def addNodeW (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : GPathM :=
  { nodes := g.nodes.map (upMapW g d forb) ++ newRowW g d title forb,
    gowners := g.gowners ++ rowIdsW g d forb,
    current_step := g.current_step + 1,
    map_parent := some d }

/-- **The bin `do_up!`**: add the row; if a window was skipped, review. -/
def upW (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : GPathM :=
  if isValid g then
    let g' := addNodeW g d title forb
    if skipsWindow g d forb then review g' else g'
  else g

/-- **The bin `do_up_filtering!`**. -/
def upFilteringW (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) : GPathM :=
  upW (filterAll g reqs) d title forb

-- ============================================================
-- With nothing prohibited it is the classic UP
-- ============================================================

theorem rowIdsW_none (g : GPathM) (d : NodeId) : rowIdsW g d (fun _ => false) = newRowIds g d := by
  simp [rowIdsW]

theorem skipsWindow_none (g : GPathM) (d : NodeId) : skipsWindow g d (fun _ => false) = false := by
  simp [skipsWindow]

/-- **The classic UP is the special case with no prohibited window.** So every lemma of
`lean_project` about `addNode` applies verbatim to the variables and the fusion nodes of the bin
map, where nothing is prohibited. -/
theorem upMapW_none (g : GPathM) (d : NodeId) :
    upMapW g d (fun _ => false) = upMap g d := by
  funext n
  simp only [upMapW, upMap, upOwners, upSons, gainedSonsW, gainedOwnersW, gainedSons,
    gainedOwners, rowIdsW_none]

theorem addNodeW_none (g : GPathM) (d : NodeId) (title : String) :
    addNodeW g d title (fun _ => false) = addNode g d title := by
  simp only [addNodeW, addNode, rowIdsW_none, newRowW, newRow, upMapW_none]

theorem upW_none (g : GPathM) (d : NodeId) (title : String) :
    upW g d title (fun _ => false) = up g d title := by
  simp only [upW, up, addNodeW_none, skipsWindow_none, Bool.false_eq_true, if_false]

/-- The same holds whenever nothing the shift produces is prohibited, which is the case at
every step of the bin map that is not the third literal of a clause. -/
theorem rowIdsW_of_none_forb (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool)
    (h : ∀ pid ∈ newRowIds g d, forb pid = false) : rowIdsW g d forb = newRowIds g d := by
  unfold rowIdsW
  rw [List.filter_eq_self]
  intro pid hpid
  simp [h pid hpid]

-- ============================================================
-- Shape of the row
-- ============================================================

theorem mem_rowIdsW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) (pid : PathNodeId) :
    pid ∈ rowIdsW g d forb ↔ pid ∈ newRowIds g d ∧ forb pid = false := by
  simp [rowIdsW]

/-- **A prohibited identifier never enters the gpath.** The disjunction as a fact of shape. -/
theorem not_forb_of_mem_rowIdsW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool)
    (pid : PathNodeId) (h : pid ∈ rowIdsW g d forb) : forb pid = false :=
  ((mem_rowIdsW g d forb pid).mp h).2

theorem rowIdsW_subset (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) (pid : PathNodeId)
    (h : pid ∈ rowIdsW g d forb) : pid ∈ newRowIds g d :=
  ((mem_rowIdsW g d forb pid).mp h).1

theorem nodup_rowIdsW (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool) :
    (rowIdsW g d forb).Nodup :=
  nodup_filter_aux _ (nodup_newRowIds g d)

theorem addNodeW_gowners (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    (addNodeW g d title forb).gowners = g.gowners ++ rowIdsW g d forb := rfl

theorem addNodeW_current (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    (addNodeW g d title forb).current_step = g.current_step + 1 := rfl

/-- **An empty row kills the gpath** (Julia's fix of error 3, `92315b1`). The hypothesis on the
global owners — none at the step being added — holds on every state the machine builds. -/
theorem isValid_addNodeW_of_nil (g : GPathM) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) (hnil : rowIdsW g d forb = []) (h0 : 0 ≤ g.current_step)
    (hg : ∀ q ∈ g.gowners, q.id.step ≠ g.current_step) :
    isValid (addNodeW g d title forb) = false := by
  have hmem : g.current_step ∈ intRange 0 ((addNodeW g d title forb).current_step - 1) := by
    rw [addNodeW_current]
    exact mem_intRange_zero _ _ h0 (by omega)
  have hno : hasStepEntry (addNodeW g d title forb).gowners g.current_step = false := by
    rw [addNodeW_gowners, hnil, List.append_nil]
    unfold hasStepEntry
    rw [List.any_eq_false]
    intro q hq
    intro hb
    exact hg q hq (eq_of_beq hb)
  -- `List.all_eq_false` would bring `Classical.choice`; go through `all_eq_true` instead.
  cases hv : isValid (addNodeW g d title forb) with
  | false => rfl
  | true =>
    unfold isValid at hv
    have := List.all_eq_true.mp hv _ hmem
    rw [hno] at this
    exact absurd this Bool.false_ne_true

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSatBin.GraphPath.Model.GPathM.addNodeW_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms addNodeW_none

/-- info: 'AbsSatBin.GraphPath.Model.GPathM.upW_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms upW_none

/-- info: 'AbsSatBin.GraphPath.Model.GPathM.isValid_addNodeW_of_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_addNodeW_of_nil

end GPathM

end AbsSatBin.GraphPath.Model
