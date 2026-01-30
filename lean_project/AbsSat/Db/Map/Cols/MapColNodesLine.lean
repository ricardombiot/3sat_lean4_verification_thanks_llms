import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.Db.Map.Docs.MapDocNode

namespace AbsSat.Db.Map.Cols.MapColNodesLine

open AbsSat.Utils.Alias
open AbsSat.Db.Map.Docs.MapDocNode

structure MapColNodesLine where
  step : Step
  table : Std.HashMap IndexNode MapDocNode
  node_ids : SetNodesId
  is_valid : Bool
deriving Repr

def new (step : Step) : MapColNodesLine :=
  {
    step := step,
    table := {},
    node_ids := {},
    is_valid := true
  }

def get_node (col_nodes : MapColNodesLine) (id : NodeId) : Option MapDocNode :=
  col_nodes.table.get? id.index

def add_node_to_line! (line : MapColNodesLine) (node : MapDocNode) : MapColNodesLine :=
  { line with
    table := line.table.insert node.id.index node,
    node_ids := line.node_ids.insert node.id
  }

section Theorems

  theorem new_step_is_correct (step : Step) : (new step).step = step := by
    simp [new]

  theorem new_is_valid (step : Step) : (new step).is_valid = true := by
    simp [new]

  theorem get_node_from_new_is_none (step : Step) (id : NodeId) :
    get_node (new step) id = none := by
    simp [get_node, new]

  theorem get_node_retrieves_inserted_element (step : Step) (node : MapDocNode) :
    let col_nodes : MapColNodesLine := { (new step) with table := (new step).table.insert node.id.index node }
    get_node col_nodes node.id = some node := by
    simp [get_node]
    -- Assuming simp solves this (since error said no goals)

end Theorems

section Examples

  def run_tests : IO Unit := do
    -- Test `new`
    let col_nodes_step_5 := new 5
    assert! col_nodes_step_5.step == 5
    assert! col_nodes_step_5.table.isEmpty
    assert! col_nodes_step_5.node_ids.isEmpty
    assert! col_nodes_step_5.is_valid == true

    -- Test `get_node` on an empty collection
    let node_id_1 : NodeId := { step := 5, index := 1 }
    assert! (get_node col_nodes_step_5 node_id_1) == none

    -- Test `get_node` on a non-empty collection
    let node_doc : MapDocNode := { id := node_id_1, title := "test", parents := {}, sons := {}, requires := {} }
    let col_nodes_with_node := { col_nodes_step_5 with table := col_nodes_step_5.table.insert node_id_1.index node_doc }
    assert! (get_node col_nodes_with_node node_id_1) == some node_doc

    IO.println "All MapColNodesLine tests passed!"

  #eval run_tests

end Examples

end AbsSat.Db.Map.Cols.MapColNodesLine
