import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.Db.Path.Cols.PathColNodes

namespace AbsSat.Db.Path.Cols.PathColLines

open AbsSat.Db.Path.Cols.PathColNodes
open AbsSat.Utils.Alias
open AbsSat.Db.Path.Docs.PathDocNode -- For PathDocNode

/--
A mutable collection of `PathColNodesLine`, indexed by `Step`. This structure
represents a set of lines, where each line is a collection of nodes at a
specific step in a path.
-/
structure PathColLines where
  table    : IO.Ref (Std.HashMap Int PathColNodesLine)
  is_valid : IO.Ref Bool

/--
Creates a new, empty `PathColLines` instance. The table is initialized as an
empty HashMap, and the `is_valid` flag is set to `true`.
-/
def new : IO PathColLines := do
  let table ← IO.mkRef ({} : Std.HashMap Int PathColNodesLine)
  let is_valid ← IO.mkRef true
  pure { table := table, is_valid := is_valid }

/--
Create a deep copy of the PathColLines.
-/
def clone (col : PathColLines) : IO PathColLines := do
  let tableVal ← col.table.get
  let isValidVal ← col.is_valid.get

  -- Recursively clone each PathColNodesLine
  -- We need to iterate over the HashMap and map values to clones
  let mut newTableVal : Std.HashMap Int PathColNodesLine := {}
  for (step, line) in tableVal.toList do
     let newLine ← PathColNodes.clone line
     newTableVal := newTableVal.insert step newLine

  let newTableRef ← IO.mkRef newTableVal
  let newIsValidRef ← IO.mkRef isValidVal

  pure { table := newTableRef, is_valid := newIsValidRef }

/--
Iterates over each `PathColNodesLine` in the `table` and applies the given
function `fn_each` to it. The primary use is to execute a side effect for
each node in the entire collection.
-/
def forEach (col_lines : PathColLines) (fn_each : PathDocNode → IO Unit) : IO Unit := do
  let table ← col_lines.table.get
  for (_, col_nodes) in table.toList do
    PathColNodes.forEach col_nodes fn_each

/--
Retrieves the `PathColNodesLine` for a given `Step`, if it exists.
-/
def getStep (col_lines : PathColLines) (step : Int) : IO (Option PathColNodesLine) := do
  let table ← col_lines.table.get
  pure (table.get? step)

/--
Iterates over the nodes of a specific `Step` and applies `fn_each` to each.
If the `Step` is not found, it prints a message and does nothing.
-/
def forEachOnStep (col_lines : PathColLines) (step : Int) (fn_each : PathDocNode → IO Unit) : IO Unit := do
  let col_nodes ← getStep col_lines step
  match col_nodes with
  | some nodes => PathColNodes.forEach nodes fn_each
  | none => IO.println s!"Step {step} not found..."

/--
Adds a `PathDocNode` to the collection. If no `PathColNodesLine` exists for
the node's step, a new one is created.
-/
def pushNode! (col_lines : PathColLines) (node : PathDocNode) : IO Unit := do
  let step := node.id.id.step
  let table ← col_lines.table.get
  let line ←
    match table.get? step with
    | some line => pure line
    | none =>
      let newLine ← PathColNodes.new step
      col_lines.table.modify (·.insert step newLine)
      pure newLine
  PathColNodes.pushNode! line node

/--
Retrieves the set of `PathNodeId`s for a given `Step`. If the step does not
exist, it returns an empty set.
-/
def getIdsStep (col_lines : PathColLines) (step : Int) : IO (Std.HashSet PathNodeId) := do
  let line? ← getStep col_lines step
  match line? with
  | some line => line.nodeIds.get
  | none => pure {}

/--
Retrieves a `PathDocNode` by its `PathNodeId`. It first finds the correct
`PathColNodesLine` using the node's step and then fetches the node from it.
-/
def getNode (col_lines : PathColLines) (id : PathNodeId) : IO (Option PathDocNode) := do
  let line? ← getStep col_lines id.id.step
  match line? with
  | some line => PathColNodes.getNode line id
  | none => pure none
/--
Merges all nodes from `linesB` into `linesA`.
-/
def union! (linesA linesB : PathColLines) : IO Unit := do
  let tableB ← linesB.table.get
  for (step, colB) in tableB.toList do
    let colA ←
      match (← linesA.table.get).get? step with
      | some col => pure col
      | none =>
        let newCol ← PathColNodes.new step
        linesA.table.modify (·.insert step newCol)
        pure newCol
    PathColNodes.union! colA colB

section Tests

/--
A newly created `PathColLines` instance should have an empty table.
-/
def check_new_table_is_empty : IO Unit := do
  let col ← new
  let table ← col.table.get
  assert! (table.isEmpty)

/--
A newly created `PathColLines` instance should be valid.
-/
def check_new_is_valid : IO Unit := do
  let col ← new
  let is_valid ← col.is_valid.get
  assert! (is_valid)

def check_clone_independence : IO Unit := do
  let col ← new
  let node₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  pushNode! col node₁

  let clonedCol ← clone col
  let node₂ := PathDocNode.new { id := { step := 1, index := 2 }, parent_id := none } ""
  pushNode! clonedCol node₂

  let table1 ← col.table.get
  let table2 ← clonedCol.table.get

  let line1 := table1.getD 1 (← PathColNodes.new 0) -- Should exist
  let line2 := table2.getD 1 (← PathColNodes.new 0) -- Should exist

  let count1 ← line1.count.get
  let count2 ← line2.count.get

  assert! (count1 == 1)
  assert! (count2 == 2)

/--
`pushNode!` should increase the table size when a new step is added.
-/
def check_pushNode_increases_table_size_on_new_step : IO Unit := do
  let col ← new
  let node₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  pushNode! col node₁
  let table ← col.table.get
  assert! (table.size == 1)
  let node₂ := PathDocNode.new { id := { step := 2, index := 1 }, parent_id := none } ""
  pushNode! col node₂
  let table ← col.table.get
  assert! (table.size == 2)

/--
`forEach` should not execute on an empty collection.
-/
def check_forEach_on_empty_is_noop : IO Unit := do
  let col ← new
  let visited ← IO.mkRef false
  forEach col (fun _ => visited.set true)
  assert! (! (← visited.get))

/--
`forEach` should visit all nodes in the collection.
-/
def check_forEach_visits_all_nodes : IO Unit := do
  let col ← new
  let node₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  let node₂ := PathDocNode.new { id := { step := 1, index := 2 }, parent_id := none } ""
  let node₃ := PathDocNode.new { id := { step := 2, index := 1 }, parent_id := none } ""
  pushNode! col node₁
  pushNode! col node₂
  pushNode! col node₃

  let visited_ids ← IO.mkRef ({} : Std.HashSet NodeId)
  forEach col (fun node => visited_ids.modify (·.insert node.id.id))

  let visited ← visited_ids.get
  assert! (visited.size == 3)
  assert! (visited.contains node₁.id.id)
  assert! (visited.contains node₂.id.id)
  assert! (visited.contains node₃.id.id)

/--
`forEachOnStep` should only visit nodes at the specified step.
-/
def check_forEachOnStep_visits_correct_nodes : IO Unit := do
  let col ← new
  let node₁_step₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  let node₂_step₁ := PathDocNode.new { id := { step := 1, index := 2 }, parent_id := none } ""
  let node₁_step₂ := PathDocNode.new { id := { step := 2, index := 1 }, parent_id := none } ""
  pushNode! col node₁_step₁
  pushNode! col node₂_step₁
  pushNode! col node₁_step₂

  let visited_ids ← IO.mkRef ({} : Std.HashSet NodeId)
  forEachOnStep col 1 (fun node => visited_ids.modify (·.insert node.id.id))

  let visited ← visited_ids.get
  assert! (visited.size == 2)
  assert! (visited.contains node₁_step₁.id.id)
  assert! (visited.contains node₂_step₁.id.id)
  assert! (!visited.contains node₁_step₂.id.id)

/--
`forEachOnStep` should not execute on a non-existent step.
-/
def check_forEachOnStep_on_invalid_step_is_noop : IO Unit := do
  let col ← new
  let node₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  pushNode! col node₁

  let visited ← IO.mkRef false
  forEachOnStep col 99 (fun _ => visited.set true)
  assert! (! (← visited.get))

/--
`getIdsStep` should return an empty set for a non-existent step.
-/
def check_getIdsStep_on_invalid_step_is_empty : IO Unit := do
  let col ← new
  let ids ← getIdsStep col 99
  assert! (ids.isEmpty)

/--
`getIdsStep` should return the correct node IDs for a given step.
-/
def check_getIdsStep_returns_correct_ids : IO Unit := do
  let col ← new
  let node₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  let node₂ := PathDocNode.new { id := { step := 1, index := 2 }, parent_id := none } ""
  let node₃ := PathDocNode.new { id := { step := 2, index := 1 }, parent_id := none } ""
  pushNode! col node₁
  pushNode! col node₂
  pushNode! col node₃

  let ids_step₁ ← getIdsStep col 1
  assert! (ids_step₁.size == 2)
  assert! (ids_step₁.contains node₁.id)
  assert! (ids_step₁.contains node₂.id)

  let ids_step₂ ← getIdsStep col 2
  assert! (ids_step₂.size == 1)
  assert! (ids_step₂.contains node₃.id)

/--
`getNode` should return `none` for a non-existent node.
-/
def check_getNode_on_invalid_id_is_none : IO Unit := do
  let col ← new
  let node? ← getNode col { id := { step := 1, index := 1 }, parent_id := none }
  assert! (node?.isNone)

/--
`getNode` should return the correct node for a valid ID.
-/
def check_getNode_returns_correct_node : IO Unit := do
  let col ← new
  let node₁ := PathDocNode.new { id := { step := 1, index := 1 }, parent_id := none } ""
  pushNode! col node₁

  let node? ← getNode col node₁.id
  match node? with
  | some node => assert! (node.id == node₁.id)
  | none => assert! (false) -- Should not happen

end Tests

section Examples

def run_tests : IO Unit := do
  -- Verify tests
  check_new_table_is_empty
  check_new_is_valid
  check_clone_independence
  check_pushNode_increases_table_size_on_new_step
  check_forEach_on_empty_is_noop
  check_forEach_visits_all_nodes
  check_forEachOnStep_visits_correct_nodes
  check_forEachOnStep_on_invalid_step_is_noop
  check_getIdsStep_on_invalid_step_is_empty
  check_getIdsStep_returns_correct_ids
  check_getNode_on_invalid_id_is_none
  check_getNode_returns_correct_node

  IO.println "All PathColLines tests passed!"

-- #eval run_tests

end Examples

end AbsSat.Db.Path.Cols.PathColLines
