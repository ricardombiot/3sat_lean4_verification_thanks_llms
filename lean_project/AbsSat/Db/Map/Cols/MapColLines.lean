import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.Db.Map.Cols.MapColNodesLine
import AbsSat.Db.Map.Docs.MapDocNode

namespace AbsSat.Db.Map.Cols.MapColLines

open AbsSat.Utils.Alias
open AbsSat.Db.Map.Cols.MapColNodesLine
open AbsSat.Db.Map.Docs.MapDocNode

structure MapColLines where
  table : Std.HashMap Step MapColNodesLine
  is_valid : Bool
deriving Repr

def new : MapColLines :=
  {
    table := {},
    is_valid := true
  }

def get_step (col_lines : MapColLines) (step : Step) : Option MapColNodesLine :=
  col_lines.table.get? step

def get_ids_step (col_lines : MapColLines) (step : Step) : SetNodesId :=
  match get_step col_lines step with
  | some line => line.node_ids
  | none => {}

def get_node (col_lines : MapColLines) (id : NodeId) : Option MapDocNode :=
  match get_step col_lines id.step with
  | some line => MapColNodesLine.get_node line id
  | none => none

def get_if_dontexiste_create_it! (col_lines : MapColLines) (step : Step) : (MapColLines × MapColNodesLine) :=
  match get_step col_lines step with
  | some line => (col_lines, line)
  | none =>
    let new_line := MapColNodesLine.new step
    let new_col := { col_lines with table := col_lines.table.insert step new_line }
    (new_col, new_line)

def push_node! (col_lines : MapColLines) (node : MapDocNode) : MapColLines :=
  let (col_lines, line) := get_if_dontexiste_create_it! col_lines node.id.step
  let updated_line := AbsSat.Db.Map.Cols.MapColNodesLine.add_node_to_line! line node
  { col_lines with table := col_lines.table.insert node.id.step updated_line }

def get_node_and_update (col_lines : MapColLines) (id : NodeId) (f : MapDocNode -> MapDocNode) : MapColLines :=
   match get_step col_lines id.step with
   | some line =>
      match MapColNodesLine.get_node line id with
      | some node =>
         let updated_node := f node
         let updated_line := AbsSat.Db.Map.Cols.MapColNodesLine.add_node_to_line! line updated_node
         { col_lines with table := col_lines.table.insert id.step updated_line }
      | none => col_lines
   | none => col_lines

def link_nodes! (col_lines : MapColLines) (parent_id : NodeId) (son_id : NodeId) : MapColLines :=
  let col_lines := get_node_and_update col_lines parent_id (fun p => add_son! p son_id)
  let col_lines := get_node_and_update col_lines son_id (fun s => add_parent! s parent_id)
  col_lines

section Theorems

  theorem get_node_from_new_is_none (id : NodeId) :
    get_node new id = none := by
    simp [get_node, get_step, new]

  -- theorem get_node_retrieves_correct_node (step : Step) (line : MapColNodesLine) (id : NodeId) :
  --   let col_lines : MapColLines := { table := (new).table.insert step line, is_valid := true }
  --   get_node col_lines id = MapColNodesLine.get_node line id := by
  --   sorry

  theorem get_ids_step_from_new_is_empty (step : Step) :
    (get_ids_step new step).isEmpty := by
    simp [get_ids_step, get_step, new]

  theorem get_ids_step_retrieves_correct_ids (step : Step) (line : MapColNodesLine) :
    let col_lines : MapColLines := { table := (new).table.insert step line, is_valid := true }
    get_ids_step col_lines step = line.node_ids := by
    simp [get_ids_step, get_step]

  theorem new_table_is_empty : (new).table.isEmpty := by
    simp [new]

  theorem new_is_valid : (new).is_valid = true := by
    simp [new]

  theorem get_step_from_new_is_none (step : Step) : get_step new step = none := by
    simp [get_step, new]

  theorem get_step_retrieves_inserted_element (step : Step) (line : MapColNodesLine) :
    let col_lines : MapColLines := { table := (new).table.insert step line, is_valid := true }
    get_step col_lines step = some line := by
    simp [get_step]

end Theorems

section Examples

  def run_tests : IO Unit := do
    IO.println "Running MapColLines tests..."
    let col_lines := new
    assert! (get_step col_lines 1).isNone
    assert! (get_ids_step col_lines 1).isEmpty

    let node1 : MapDocNode := { id := { step := 1, index := 10 }, title := "test", parents := {}, sons := {}, requires := {} }
    let line1 := MapColNodesLine.new 1
    let line1 := { line1 with table := line1.table.insert 10 node1 }
    let line1 := { line1 with node_ids := line1.node_ids.insert node1.id }

    let col_lines_with_data : MapColLines := { table := (new).table.insert 1 line1, is_valid := true }

    let retrieved_line := get_step col_lines_with_data 1
    assert! retrieved_line.isSome

    let node_ids := get_ids_step col_lines_with_data 1
    assert! !node_ids.isEmpty
    assert! node_ids.contains node1.id

    let retrieved_node := get_node col_lines_with_data node1.id
    assert! retrieved_node.isSome
    match retrieved_node with
    | some n => assert! n.id == node1.id
    | none => assert! false

    let non_existent_node_id : NodeId := { step := 1, index := 99 }
    assert! (get_node col_lines_with_data non_existent_node_id).isNone

    let non_existent_step_id : NodeId := { step := 2, index := 10 }
    assert! (get_node col_lines_with_data non_existent_step_id).isNone

    IO.println "All MapColLines tests passed!"

  -- Run tests
  #eval run_tests

end Examples

end AbsSat.Db.Map.Cols.MapColLines
