import Std.Data.HashMap
import Std.Data.HashSet
import AbsSat.Utils.Alias
import AbsSat.Db.Path.Docs.PathDocNode

namespace AbsSat.Db.Path.Cols.PathColNodes

open AbsSat.Utils.Alias
open AbsSat.Db.Path.Docs.PathDocNode

abbrev Table := Std.HashMap PathNodeId PathDocNode

/--
Mutable collection of path documentation nodes.
-/
structure PathColNodesLine where
  step     : Int
  table    : IO.Ref Table
  nodeIds  : IO.Ref (Std.HashSet PathNodeId)
  count    : IO.Ref Int
  isValid  : IO.Ref Bool

/--
Create a new empty PathColNodesLine for the given step.
-/
def new (step : Int) : IO PathColNodesLine := do
  let table   ← IO.mkRef ({} : Table)
  let nodeIds ← IO.mkRef ({} : Std.HashSet PathNodeId)
  let count   ← IO.mkRef 0
  let isValid ← IO.mkRef true
  pure { step, table, nodeIds, count, isValid }

/--
Create a deep copy of the PathColNodesLine.
-/
def clone (col : PathColNodesLine) : IO PathColNodesLine := do
  let tableVal   ← col.table.get
  let nodeIdsVal ← col.nodeIds.get
  let countVal   ← col.count.get
  let isValidVal ← col.isValid.get

  -- Create new Refs with copied values
  -- Note: PathDocNode is a structure (value type), and Std.HashMap/HashSet are persistent (value types),
  -- so reading them from the Ref and putting them in a new Ref effectively treats them as deep copies
  -- relative to the mutable Ref container.
  -- Warning: If PathDocNode contains IO.Ref, this shallow copy of values is insufficient.
  -- Checking PathDocNode: It has `owners: PathDocOwners`. PathDocOwners has `table: HashMap`.
  -- So PathDocNode is value type. Safe to just copy the value into new Ref.

  let newTable   ← IO.mkRef tableVal
  let newNodeIds ← IO.mkRef nodeIdsVal
  let newCount   ← IO.mkRef countVal
  let newIsValid ← IO.mkRef isValidVal

  pure { step := col.step, table := newTable, nodeIds := newNodeIds, count := newCount, isValid := newIsValid }

/--
Iterate over all nodes in the collection.
-/
def forEach (col : PathColNodesLine) (f : PathDocNode → IO Unit) : IO Unit := do
  let t ← col.table.get
  for (_, node) in t.toList do
    f node

/--
Remove a node by id.
-/
def removeNode! (col : PathColNodesLine) (id : PathNodeId) : IO Unit := do
  col.table.modify fun t => t.erase id
  col.nodeIds.modify fun s => s.erase id
  col.count.modify (· - 1)

/--
Filter nodes in place by a predicate.
-/
def filter! (col : PathColNodesLine) (pred : PathDocNode → Bool) : IO Unit := do
  let t ← col.table.get
  for item in t.toList do
    let id := item.fst
    let node := item.snd
    if pred node then
      removeNode! col id

/--
Get a node by id.
-/
def getNode (col : PathColNodesLine) (id : PathNodeId) : IO (Option PathDocNode) := do
  let t ← col.table.get
  pure (t.get? id)

/--
Push a node into the collection.
-/
def pushNode! (col : PathColNodesLine) (node : PathDocNode) : IO Unit := do
  col.table.modify fun t => t.insert node.id node
  col.nodeIds.modify fun s => s.insert node.id
  col.count.modify (· + 1)


/--
Check if collection is empty.
-/
def isEmpty (col : PathColNodesLine) : IO Bool := do
  let c ← col.count.get
  pure (c = 0)

def union! (colA colB : PathColNodesLine) : IO Unit := do
  let tB ← colB.table.get
  for (_, nodeB) in tB.toList do
    let nodeA? ← getNode colA nodeB.id
    match nodeA? with
    | some nodeA =>
       let merged := PathDocNode.union nodeA nodeB
       colA.table.modify fun t => t.insert merged.id merged
    | none =>
       pushNode! colA nodeB

section Tests

  def check_new_initial_state_is_correct (step : Nat) : IO Bool := do
    let col ← new step
    let table ← col.table.get
    let count ← col.count.get
    pure $ col.step == step ∧ table.isEmpty ∧ count == 0

  def check_new_is_valid_by_default (step : Nat) : IO Bool := do
    let col ← new step
    let isValid ← col.isValid.get
    pure isValid

  def check_clone_independence : IO Bool := do
    let col ← new 1
    let nodeId : PathNodeId := { id := { step := 1, index := 0 }, parent_id := none }
    let docNode := PathDocNode.new nodeId "original"
    pushNode! col docNode

    let clonedCol ← clone col
    let nodeId2 : PathNodeId := { id := { step := 1, index := 1 }, parent_id := none }
    let docNode2 := PathDocNode.new nodeId2 "modified"
    pushNode! clonedCol docNode2

    let count1 ← col.count.get
    let count2 ← clonedCol.count.get

    -- Original should have 1, Clone should have 2
    pure (count1 == 1 ∧ count2 == 2)

  def check_forEach_on_empty_col_is_vacuously_true : IO Bool := do
    let col ← new 0
    let ref ← IO.mkRef true
    forEach col fun _ => do
      ref.set false
    ref.get

  def check_forEach_iterates_over_all_elements : IO Bool := do
    let step := 1
    let col ← new step
    let id1 : PathNodeId := { id := { step := step, index := 0 }, parent_id := none }
    let id2 : PathNodeId := { id := { step := step, index := 1 }, parent_id := some id1.id }
    let node1 := PathDocNode.new id1 "node1"
    let node2 := PathDocNode.new id2 "node2"
    pushNode! col node1
    pushNode! col node2
    let ref ← IO.mkRef #[]
    forEach col fun node => do
      ref.modify fun arr => arr.push node.id
    let visitedIds ← ref.get
    let expectedIds := #[id1, id2].qsort (·.id.index < ·.id.index)
    let actualIds := visitedIds.qsort (·.id.index < ·.id.index)
    return expectedIds == actualIds

  def check_getNode_on_empty_col_returns_none : IO Bool := do
    let col ← new 0
    let nodeId : PathNodeId := { id := { step := 0, index := 0 }, parent_id := none }
    let result ← getNode col nodeId
    pure $ result.isNone

  def check_getNode_after_pushNode_returns_some : IO Bool := do
    let step := 1
    let col ← new step
    let nodeId : PathNodeId := { id := { step := step, index := 0 }, parent_id := none }
    let docNode := PathDocNode.new nodeId "node"
    pushNode! col docNode
    let result ← getNode col nodeId
    pure $ result.isSome ∧ result.get!.id == nodeId

  def check_isEmpty_on_new_col_is_true : IO Bool := do
    let col ← new 0
    isEmpty col

  def check_isEmpty_after_pushNode_is_false : IO Bool := do
    let step := 1
    let col ← new step
    let nodeId : PathNodeId := { id := { step := step, index := 0 }, parent_id := none }
    let docNode := PathDocNode.new nodeId "node"
    pushNode! col docNode
    let result ← isEmpty col
    pure (not result)

end Tests

section Examples

  def run_tests : IO Unit := do
    -- Verify tests
    assert! (← check_new_initial_state_is_correct 10)
    assert! (← check_new_is_valid_by_default 10)
    assert! (← check_clone_independence)
    assert! (← check_forEach_on_empty_col_is_vacuously_true)
    assert! (← check_forEach_iterates_over_all_elements)
    assert! (← check_getNode_on_empty_col_returns_none)
    assert! (← check_getNode_after_pushNode_returns_some)
    assert! (← check_isEmpty_on_new_col_is_true)
    assert! (← check_isEmpty_after_pushNode_is_false)

    IO.println "All PathColNodesLine tests passed!"

  -- Run tests
  #eval run_tests

end Examples

end AbsSat.Db.Path.Cols.PathColNodes
