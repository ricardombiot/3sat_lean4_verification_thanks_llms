import AbsSat.Utils.Alias
import AbsSat.GraphMap.GraphMap
import AbsSat.Db.Map.Cols.MapColLines
import AbsSat.Db.Map.Docs.MapDocNode
import Std.Data.HashSet

namespace AbsSat.GraphMap.Visual

open AbsSat.Utils.Alias
open AbsSat.GraphMap.GraphMap
open AbsSat.Db.Map.Cols.MapColLines
open AbsSat.Db.Map.Docs.MapDocNode

structure MapDiagram where
  graph : GMap
  dot_txt : String
deriving Repr

def to_list (set_nodes_id : Std.HashSet NodeId) : String :=
  let sorted_nodes := set_nodes_id.toArray.qsort (fun a b => as_key a < as_key b)
  let keys := sorted_nodes.map (fun node_id => (as_key node_id) ++ ",")
  String.intercalate "" keys.toList

def draw_node! (node : MapDocNode) : String :=
  let key := as_key node.id
  let key_node := s!"k{node.id.step}_{node.id.index}"
  let list_requires := to_list node.requires
  let node_label_html := s!"<{node.title}<BR /> ID: {key} <BR />Requires: [{list_requires}] <BR />>"
  s!"{key_node} [label={node_label_html}]"

def draw_relations! (diagram : MapDiagram) : String := Id.run do
  let mut relations_txt := ""
  for step in [0:diagram.graph.step.toNat] do
    for node_id in get_ids_step diagram.graph step do
      match AbsSat.Db.Map.Cols.MapColLines.get_node diagram.graph.table_lines node_id with
      | some node =>
        let key_origin := s!"k{node_id.step}_{node_id.index}"
        for node_id_son in node.sons do
          let key_destine := s!"k{node_id_son.step}_{node_id_son.index}"
          relations_txt := relations_txt ++ s!"{key_origin} -> {key_destine}" ++ "\n"
      | none => ()
  return relations_txt

def draw_line! (diagram : MapDiagram) (step : Int) : String := Id.run do
  let id := step
  let mut subgraph_txt := ""
  subgraph_txt := subgraph_txt ++ s!"subgraph cluster_line_{id} " ++ "{\n"
  subgraph_txt := subgraph_txt ++ " style=filled;\n"
  subgraph_txt := subgraph_txt ++ " color=lightgrey; \n"
  subgraph_txt := subgraph_txt ++ "     node [style=filled,color=white]; \n"
  for node_id in get_ids_step diagram.graph step do
    match AbsSat.Db.Map.Cols.MapColLines.get_node diagram.graph.table_lines node_id with
    | some node =>
      subgraph_txt := subgraph_txt ++ draw_node! node
    | none => ()
  subgraph_txt := subgraph_txt ++ "\n"
  subgraph_txt := subgraph_txt ++ "     fontsize=\"12\" \n"
  subgraph_txt := subgraph_txt ++ s!"     label = \"Line {id} \" \n"
  subgraph_txt := subgraph_txt ++ " }\n"
  return subgraph_txt

def draw! (diagram : MapDiagram) : String := Id.run do
  let mut draw_txt := ""
  for i in [0:diagram.graph.step.toNat] do
    draw_txt := draw_txt ++ draw_line! diagram i
  return draw_txt

def build_diagram! (diagram : MapDiagram) : MapDiagram :=
  let dot_txt := "digraph G {\n"
  let dot_txt := dot_txt ++ "     compound=true \n"
  let dot_txt := dot_txt ++ draw! diagram
  let dot_txt := dot_txt ++ draw_relations! diagram
  let dot_txt := dot_txt ++ "}"
  { diagram with dot_txt := dot_txt }

def build (graph : GMap) : MapDiagram :=
  let diagram := MapDiagram.mk graph ""
  build_diagram! diagram

def to_dot_file_content (diagram : MapDiagram) : String :=
  diagram.dot_txt

def to_png (diagram : MapDiagram) (name : String) (path : String := "./test_visual") : IO Unit := do
  let input_file := s!"{path}/{name}.dot"
  -- let output_file := s!"{path}/{name}.png"
  let dot_content := to_dot_file_content diagram
  IO.FS.writeFile input_file dot_content
  -- Skip dot command
  IO.println s!"Generated DOT file at {input_file}"
  return ()

section Examples
  def run_tests : IO Unit := do
    IO.println "Running Visual tests..."
    let gmap ← AbsSat.GraphMap.GraphMap.new
    let diagram := build gmap
    -- IO.println diagram.dot_txt
    IO.println s!"Generated diagram with {diagram.dot_txt.length} bytes"
    IO.println "Visual tests passed!"
  #eval run_tests
end Examples

end AbsSat.GraphMap.Visual
