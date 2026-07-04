import AbsSat.Utils.Alias
import AbsSat.Db.Path.Cols.PathColLines
import AbsSat.Db.Path.Cols.PathColNodes
import AbsSat.Db.Path.Docs.PathDocOwners
import AbsSat.Db.Path.Docs.PathDocNode
import Std.Data.HashSet

namespace AbsSat.GraphPath

open AbsSat.Utils.Alias

-- Define type aliases
abbrev PColLines := AbsSat.Db.Path.Cols.PathColLines.PathColLines
abbrev PDocOwners := AbsSat.Db.Path.Docs.PathDocOwners.PathDocOwners
abbrev PDocNode := AbsSat.Db.Path.Docs.PathDocNode.PathDocNode

-- Open function namespaces
open AbsSat.Db.Path.Docs.PathDocOwners -- Contains isValid, remove, insert, intersect
open AbsSat.Db.Path.Docs.PathDocNode.PathDocNode -- Contains is_valid, is_root, removeSon, removeParent, putOwners, addOwner, addParent, addSon
open AbsSat.Db.Path.Cols.PathColLines -- Contains getNode, pushNode!, getIdsStep, forEach

structure GPath : Type where
  table_lines   : PColLines
  owners        : IO.Ref PDocOwners
  current_step  : IO.Ref Step
  map_parent_id : IO.Ref (Option NodeId)
  review_owners : IO.Ref Bool
  is_valid      : IO.Ref Bool

namespace GPath

def new : IO GPath := do
  let lines ← AbsSat.Db.Path.Cols.PathColLines.new
  let owners ← IO.mkRef AbsSat.Db.Path.Docs.PathDocOwners.new
  let step ← IO.mkRef 0
  let parent ← IO.mkRef none
  let review ← IO.mkRef false
  let valid ← IO.mkRef true
  pure {
    table_lines := lines,
    owners := owners,
    current_step := step,
    map_parent_id := parent,
    review_owners := review,
    is_valid := valid
  }

def clone (gpath : GPath) : IO GPath := do
  let lines ← AbsSat.Db.Path.Cols.PathColLines.clone gpath.table_lines

  -- Clone owners (Deep copy of helper struct, put in new Ref)
  let ownersVal ← gpath.owners.get
  let newOwnersVal := AbsSat.Db.Path.Docs.PathDocOwners.clone ownersVal
  let owners ← IO.mkRef newOwnersVal

  -- Scalars/Immutables in Refs need new Refs
  let stepVal ← gpath.current_step.get
  let step ← IO.mkRef stepVal

  let parentVal ← gpath.map_parent_id.get
  let parent ← IO.mkRef parentVal

  let reviewVal ← gpath.review_owners.get
  let review ← IO.mkRef reviewVal

  let validVal ← gpath.is_valid.get
  let valid ← IO.mkRef validVal

  pure {
    table_lines := lines,
    owners := owners,
    current_step := step,
    map_parent_id := parent,
    review_owners := review,
    is_valid := valid
  }

end GPath

def is_valid_node (gpath : GPath) (path_node : PDocNode) : IO Bool := do
  let is_owners_valid := AbsSat.Db.Path.Docs.PathDocNode.PathDocNode.is_valid path_node
  let is_root_node := is_root path_node
  let current_step ← gpath.current_step.get
  let is_in_last_step := get_step path_node == current_step - 1
  let have_parents := !path_node.parents.isEmpty
  let have_sons := !path_node.sons.isEmpty

  if is_root_node then
    if is_in_last_step then
       pure is_owners_valid
    else
       pure (is_owners_valid && have_sons)
  else if is_in_last_step then
       pure (is_owners_valid && have_parents)
  else
       pure (is_owners_valid && have_parents && have_sons)

def check_if_graph_valid! (gpath : GPath) : IO Unit := do
  let owners ← gpath.owners.get
  gpath.is_valid.set (AbsSat.Db.Path.Docs.PathDocOwners.isValid owners)

def remove_node_owner! (gpath : GPath) (path_node_id : PathNodeId) : IO Unit := do
  gpath.owners.modify (fun o => AbsSat.Db.Path.Docs.PathDocOwners.remove o path_node_id)
  check_if_graph_valid! gpath

def clean_links! (gpath : GPath) (path_node : PDocNode) : IO Unit := do
  for node_id_parent in path_node.parents do
    let node_parent? ← getNode gpath.table_lines node_id_parent
    match node_parent? with
    | some node_parent =>
       let updated_parent := removeSon node_parent path_node.id
       pushNode! gpath.table_lines updated_parent
    | none => pure ()

  for node_id_son in path_node.sons do
    let node_son? ← getNode gpath.table_lines node_id_son
    match node_son? with
    | some node_son =>
       let updated_son := removeParent node_son path_node.id
       pushNode! gpath.table_lines updated_son
    | none => pure ()

def remove_if_invalid_node! (gpath : GPath) (path_node : PDocNode) : IO Bool := do
  let is_valid ← is_valid_node gpath path_node
  if !is_valid then
    remove_node_owner! gpath path_node.id
    clean_links! gpath path_node
    gpath.review_owners.set true
    pure true
  else
    pure false

def clean_invalid_nodes! (gpath : GPath) : IO Unit := do
  AbsSat.Db.Path.Cols.PathColLines.filter! gpath.table_lines (fun map_node => do
    let owners ← gpath.owners.get
    let updated_owners := AbsSat.Db.Path.Docs.PathDocOwners.intersect map_node.owners owners
    let map_node := putOwners map_node updated_owners
    pushNode! gpath.table_lines map_node

    remove_if_invalid_node! gpath map_node
  )

/--
Union the owners tables of every node named by `ids` (looked up in the
graph's current node collection). Returns `none` when `ids` is empty. Mirrors
the `owners_union_parents`/`owners_union_sons` accumulation loops in Julia's
`review_owners_parents_sons!`/`review_owners_sons_parents!`.
-/
def union_owners_of! (gpath : GPath) (ids : Std.HashSet PathNodeId) : IO (Option PDocOwners) := do
  let mut acc? : Option PDocOwners := none
  for neighbor_id in ids do
    let neighbor? ← getNode gpath.table_lines neighbor_id
    match neighbor? with
    | some neighbor =>
      acc? := some (match acc? with
        | some acc => AbsSat.Db.Path.Docs.PathDocOwners.union acc neighbor.owners
        | none => neighbor.owners)
    | none => pure ()
  pure acc?

/--
Enforce owners-coherence for a single line/step against a chosen set of
neighbors (parents on the top-down pass, sons on the bottom-up pass): each
still-valid node's owners are intersected with the union of its neighbors'
owners, and the node is dropped if that leaves it invalid. Mirrors the shared
body of Julia's `review_owners_parents_sons!`/`review_owners_sons_parents!`.
-/
def review_owners_line! (gpath : GPath) (neighbors : PDocNode → Std.HashSet PathNodeId) (step : Int) : IO Unit := do
  let col_nodes? ← getStep gpath.table_lines step
  match col_nodes? with
  | some col_nodes =>
    AbsSat.Db.Path.Cols.PathColNodes.filter! col_nodes (fun path_node => do
      let node_is_valid ← is_valid_node gpath path_node
      if node_is_valid then
        let owners_union? ← union_owners_of! gpath (neighbors path_node)
        match owners_union? with
        | some owners_union =>
          let updated_owners := AbsSat.Db.Path.Docs.PathDocOwners.intersect path_node.owners owners_union
          let updated_node := putOwners path_node updated_owners
          pushNode! gpath.table_lines updated_node
          remove_if_invalid_node! gpath updated_node
        | none =>
          remove_if_invalid_node! gpath path_node
      else
        remove_if_invalid_node! gpath path_node
    )
    AbsSat.Db.Path.Cols.PathColLines.checkIfValidLine! gpath.table_lines step
    check_if_graph_valid! gpath
  | none => pure ()

partial def review_owners_ascending! (gpath : GPath) (neighbors : PDocNode → Std.HashSet PathNodeId) (step upper : Int) : IO Unit := do
  if step > upper then
    pure ()
  else
    review_owners_line! gpath neighbors step
    let valid ← gpath.is_valid.get
    if valid then
      review_owners_ascending! gpath neighbors (step + 1) upper

partial def review_owners_descending! (gpath : GPath) (neighbors : PDocNode → Std.HashSet PathNodeId) (step lower : Int) : IO Unit := do
  if step < lower then
    pure ()
  else
    review_owners_line! gpath neighbors step
    let valid ← gpath.is_valid.get
    if valid then
      review_owners_descending! gpath neighbors (step - 1) lower

/--
Top-down pass: intersect every node's owners with the union of its parents'
owners, one step at a time from 1 to current_step-1. Mirrors Julia's
`review_owners_parents_sons!`.
-/
def review_owners_parents_sons! (gpath : GPath) : IO Unit := do
  let valid ← gpath.is_valid.get
  let review ← gpath.review_owners.get
  if valid && review then
    let current_step ← gpath.current_step.get
    review_owners_ascending! gpath (fun n => n.parents) 1 (current_step - 1)

/--
Bottom-up pass: intersect every node's owners with the union of its sons'
owners, one step at a time from current_step-2 down to 1. Mirrors Julia's
`review_owners_sons_parents!`.
-/
def review_owners_sons_parents! (gpath : GPath) : IO Unit := do
  let valid ← gpath.is_valid.get
  let review ← gpath.review_owners.get
  if valid && review then
    let current_step ← gpath.current_step.get
    review_owners_descending! gpath (fun n => n.sons) (current_step - 2) 1

/--
Los owners deben ser coherentes con sus padres e hijos: run both the
top-down and bottom-up coherence passes. Mirrors Julia's
`review_owners_coherence_with_its_parents_sons!`.
-/
def review_owners_coherence_with_its_parents_sons! (gpath : GPath) : IO Unit := do
  review_owners_parents_sons! gpath
  review_owners_sons_parents! gpath

partial def make_review_owners! (gpath : GPath) : IO Unit := do
  let valid ← gpath.is_valid.get
  let review ← gpath.review_owners.get
  if valid && review then
    gpath.review_owners.set false
    clean_invalid_nodes! gpath
    review_owners_coherence_with_its_parents_sons! gpath

    let review_again ← gpath.review_owners.get
    if review_again then
       make_review_owners! gpath

def filter_require! (gpath : GPath) (map_node_id_req : NodeId) : IO Unit := do
  let valid ← gpath.is_valid.get
  if valid then
    let step_selection := map_node_id_req.step
    let nodes_ids ← getIdsStep gpath.table_lines step_selection

    for node_id in nodes_ids do
      let is_required := node_id.id == map_node_id_req
      if !is_required then
         remove_node_owner! gpath node_id
         gpath.review_owners.set true

    check_if_graph_valid! gpath

def filter! (gpath : GPath) (requires : Std.HashSet NodeId) : IO Unit := do
  for map_node_id in requires do
    filter_require! gpath map_node_id
  make_review_owners! gpath

def all_previous_nodes_are_owners_of_me! (gpath : GPath) (node : PDocNode) : IO Unit := do
  forEach gpath.table_lines (fun node_previous => do
     let updated_prev := addOwner node_previous node.id
     pushNode! gpath.table_lines updated_prev
  )

def create_node! (gpath : GPath) (map_id_node : NodeId) (title : String) : IO PDocNode := do
  let current_parent_id ← gpath.map_parent_id.get
  let path_id_node : PathNodeId := { id := map_id_node, parent_id := current_parent_id }
  pure (AbsSat.Db.Path.Docs.PathDocNode.PathDocNode.new path_id_node title)

def link_with_parents! (gpath : GPath) (node : PDocNode) : IO PDocNode := do
  let current_step ← gpath.current_step.get
  if current_step > 0 then
    let last_step := current_step - 1
    let parent_ids ← getIdsStep gpath.table_lines last_step

    let mut node_acc := node
    for parent_id in parent_ids do
       node_acc := addParent node_acc parent_id

       let parent_node? ← getNode gpath.table_lines parent_id
       if let some parent_node := parent_node? then
          let updated_parent := addSon parent_node node.id
          pushNode! gpath.table_lines updated_parent

    pure node_acc
  else
    pure node

def add_node! (gpath : GPath) (map_id_node : NodeId) (title : String) : IO Unit := do
   let node ← create_node! gpath map_id_node title
   let node ← link_with_parents! gpath node

   let owners ← gpath.owners.get
   let node := putOwners node owners

   pushNode! gpath.table_lines node

   gpath.owners.modify (fun o => AbsSat.Db.Path.Docs.PathDocOwners.insert o node.id)
   all_previous_nodes_are_owners_of_me! gpath node

def do_up! (gpath : GPath) (map_id_node : NodeId) (title : String) : IO Unit := do
  let valid ← gpath.is_valid.get
  if valid then
     add_node! gpath map_id_node title
     gpath.current_step.modify (· + 1)
     gpath.map_parent_id.set (some map_id_node)

def do_up_filtering! (gpath : GPath) (requires : Std.HashSet NodeId) (map_id_node : NodeId) (title : String) : IO Unit := do
  filter! gpath requires
  do_up! gpath map_id_node title

def is_valid_join (gpath : GPath) (gpath_inmutable : GPath) : IO Bool := do
  let parent1 ← gpath.map_parent_id.get
  let parent2 ← gpath_inmutable.map_parent_id.get
  let eq_parent := parent1 == parent2

  let step1 ← gpath.current_step.get
  let step2 ← gpath_inmutable.current_step.get
  let eq_step := step1 == step2

  let valid1 ← gpath.is_valid.get
  let valid2 ← gpath_inmutable.is_valid.get
  let both_valid := valid1 && valid2

  pure (eq_parent && eq_step && both_valid)

def do_join! (gpath : GPath) (gpath_inmutable : GPath) : IO Unit := do
  let valid ← is_valid_join gpath gpath_inmutable
  if valid then
     -- Deep copy of immutable path to ensure isolation (optional if union! works with source refs safely,
     -- but safer to follow Julia logic if side effects exist).
     -- Actually, union! only reads from source. Cloning might be redundant if source is truly immutable during join.
     -- Julia uses deepcopy, probably to avoid sharing structure pointers if union! was destructive or link-based?
     -- Or maybe just to be safe. In Lean with Refs, if we modify gpath, we don't assume we modify gpath_inmutable.
     -- union! modifies 'gpath' (linesA), reads 'gpath_inmutable' (linesB).
     -- Seems safe to read directly?
     -- But `owners` union?
     -- PathDocOwners.union (a b) returns new structure.
     -- So we just set it.

     -- Let's just use gpath_inmutable directly for reading.

     AbsSat.Db.Path.Cols.PathColLines.union! gpath.table_lines gpath_inmutable.table_lines

     let ownersB ← gpath_inmutable.owners.get
     gpath.owners.modify (fun ownersA => AbsSat.Db.Path.Docs.PathDocOwners.union ownersA ownersB)



section Examples

  def check_do_join_merges_data : IO Unit := do
     -- Setup path1
     let path1 ← GPath.new
     add_node! path1 { step := 0, index := 1 } "root1"

     -- Setup path2 (clone of path1 + new node)
     let path2 ← GPath.clone path1
     add_node! path2 { step := 0, index := 2 } "root2"

     -- Verify initial state
     let lines1_ref ← path1.table_lines.table.get
     let line1_opt := lines1_ref.get? 0
     if let some line1 := line1_opt then
       let count1 ← line1.count.get
       if count1 != 1 then IO.println s!"Error: Initial count is {count1}, expected 1" else pure ()

     -- Perform Join
     let valid ← is_valid_join path1 path2
     if !valid then IO.println "Join invalid!" else pure ()

     do_join! path1 path2

     -- Verify Merge
     let lines1_final_ref ← path1.table_lines.table.get
     let line1_final_opt := lines1_final_ref.get? 0
     if let some line1_final := line1_final_opt then
       let count1_final ← line1_final.count.get
       if count1_final != 2 then
         IO.println s!"Error: Final count is {count1_final}, expected 2"
       else
         IO.println "check_do_join_merges_data passed!"
     else
         IO.println "Error: Line 0 missing after join"

  def run_tests : IO Unit := do
    check_do_join_merges_data

  #eval run_tests

end Examples

end AbsSat.GraphPath
