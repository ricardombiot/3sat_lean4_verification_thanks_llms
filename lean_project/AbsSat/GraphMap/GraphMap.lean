import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.Db.Map.Cols.MapColLines
import AbsSat.Db.Map.Cols.MapColVars
import AbsSat.Db.Map.Docs.MapDocNode

namespace AbsSat.GraphMap.GraphMap

open AbsSat.Utils.Alias
open AbsSat.Db.Map.Cols.MapColLines
open AbsSat.Db.Map.Cols.MapColVars
open AbsSat.Db.Map.Docs.MapDocNode

structure GMap where
  table_lines : MapColLines
  table_vars : MapColVars
  literals_counter : Nat
  clausule_counter : Nat
  stage : String
  step : Step
deriving Repr

def new : IO GMap := do
  let table_lines := AbsSat.Db.Map.Cols.MapColLines.new
  let table_vars ← AbsSat.Db.Map.Cols.MapColVars.new
  return {
    table_lines := table_lines,
    table_vars := table_vars,
    literals_counter := 0,
    clausule_counter := 0,
    stage := "vars",
    step := 0
  }

def get_ids_step (gmap : GMap) (step : Step) : SetNodesId :=
  AbsSat.Db.Map.Cols.MapColLines.get_ids_step gmap.table_lines step

def get_node (gmap : GMap) (id : NodeId) : Option MapDocNode :=
   AbsSat.Db.Map.Cols.MapColLines.get_node gmap.table_lines id

def get_ids_last_step (gmap : GMap) : SetNodesId :=
  if gmap.step > 0 then
    get_ids_step gmap (gmap.step - 1)
  else
    {}

def for_each_node_step (gmap : GMap) (step : Step) (f : MapDocNode → IO Unit) : IO Unit := do
  let ids := get_ids_step gmap step
  for id in ids do
    match get_node gmap id with
    | some node => f node
    | none => pure ()

def add_var! (gmap : GMap) (title : String) : IO GMap := do
  if gmap.stage == "vars" then
    let var_step := gmap.step
    register_var! gmap.table_vars title var_step
    let var_neg_step := var_step + 1
    let var_parents := get_ids_last_step gmap

    -- Positive Variable Nodes
    let id0 : NodeId := { step := var_step, index := 0 }
    let node0 := AbsSat.Db.Map.Docs.MapDocNode.new id0 s!"{title}=0"
    let node0 := add_son! node0 ({ step := var_neg_step, index := 1 } : NodeId)

    let id1 : NodeId := { step := var_step, index := 1 }
    let node1 := AbsSat.Db.Map.Docs.MapDocNode.new id1 s!"{title}=1"
    let node1 := add_son! node1 ({ step := var_neg_step, index := 0 } : NodeId)

    let mut table_lines := push_node! gmap.table_lines node0
    table_lines := push_node! table_lines node1

    for parent_id in var_parents do
      table_lines := link_nodes! table_lines parent_id node0.id
      table_lines := link_nodes! table_lines parent_id node1.id

    -- Negative Variable Nodes
    let id0_neg : NodeId := { step := var_neg_step, index := 0 }
    let mut node0_neg := AbsSat.Db.Map.Docs.MapDocNode.new id0_neg s!"!{title}=0"
    node0_neg := add_parent! node0_neg { step := var_step, index := 1 }
    node0_neg := add_require! node0_neg { step := var_step, index := 1 }
    table_lines := push_node! table_lines node0_neg

    let id1_neg : NodeId := { step := var_neg_step, index := 1 }
    let mut node1_neg := AbsSat.Db.Map.Docs.MapDocNode.new id1_neg s!"!{title}=1"
    node1_neg := add_parent! node1_neg { step := var_step, index := 0 }
    node1_neg := add_require! node1_neg { step := var_step, index := 0 }
    table_lines := push_node! table_lines node1_neg

    return { gmap with
      table_lines := table_lines,
      step := gmap.step + 2,
      literals_counter := gmap.literals_counter + 2
    }
  else
    return gmap

def make_fusion_node! (gmap : GMap) : GMap :=
  let node_fusion := AbsSat.Db.Map.Docs.MapDocNode.new { step := gmap.step, index := 0 } "FusionNode"
  let table_lines := push_node! gmap.table_lines node_fusion

  let table_lines := get_ids_last_step gmap |>.fold (fun lines parent_id =>
    link_nodes! lines parent_id node_fusion.id
  ) table_lines

  { gmap with
    table_lines := table_lines,
    step := gmap.step + 1
  }

def close_vars! (gmap : GMap) : GMap :=
  if gmap.stage == "vars" then
    let gmap := make_fusion_node! gmap
    { gmap with stage := "gates" }
  else
    gmap

def close_gates! (gmap : GMap) : GMap :=
  if gmap.stage == "gates" then
    let gmap := make_fusion_node! gmap
    { gmap with stage := "end" }
  else
    gmap

def add_gate_case! (gmap : GMap) (step_a step_b step_c : Step) (case_str : String) : GMap :=
  match case_str.toNat? with
  | none => gmap
  | some _ =>
    let chars := case_str.toList
    let index : Int :=
      let c1 := if chars.getD 0 '0' == '1' then 4 else 0
      let c2 := if chars.getD 1 '0' == '1' then 2 else 0
      let c3 := if chars.getD 2 '0' == '1' then 1 else 0
      c1 + c2 + c3

    let title_or := s!"or{gmap.clausule_counter}"
    let node_gate := AbsSat.Db.Map.Docs.MapDocNode.new { step := gmap.step, index := index } s!"{title_or}={case_str}"

    let target_index_a := if chars.getD 0 '0' == '0' then 0 else 1
    let target_index_b := if chars.getD 1 '0' == '0' then 0 else 1
    let target_index_c := if chars.getD 2 '0' == '0' then 0 else 1

    let node_gate := add_require! node_gate { step := step_a, index := target_index_a }
    let node_gate := add_require! node_gate { step := step_b, index := target_index_b }
    let node_gate := add_require! node_gate { step := step_c, index := target_index_c }

    let table_lines := push_node! gmap.table_lines node_gate

    let table_lines := get_ids_last_step gmap |>.fold (fun lines parent_id =>
      link_nodes! lines parent_id node_gate.id
    ) table_lines

    { gmap with table_lines := table_lines }

partial def add_gate! (gmap : GMap) (title_a title_b title_c : String) : IO GMap := do
  if gmap.stage == "gates" then
    let step_a ← get_step_var gmap.table_vars title_a
    let step_b ← get_step_var gmap.table_vars title_b
    let step_c ← get_step_var gmap.table_vars title_c

    match step_a, step_b, step_c with
    | some a, some b, some c =>
      let valid_cases := ["001","010","011","100","101","110","111"]
      let mut gmap_acc := gmap
      for c_str in valid_cases do
        gmap_acc := add_gate_case! gmap_acc a b c c_str

      return { gmap_acc with
        clausule_counter := gmap_acc.clausule_counter + 1,
        step := gmap_acc.step + 1
      }
    | _, _, _ =>
       IO.println "Error: Missing vars for gate"
       return gmap
  else
    let gmap := close_vars! gmap
    add_gate! gmap title_a title_b title_c

end AbsSat.GraphMap.GraphMap
