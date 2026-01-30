import Std.Data.HashMap
import Std.Data.HashSet
import AbsSat.Utils.Alias

namespace AbsSat.GraphPow

open AbsSat.Utils.Alias

structure GPow where
  lines_table     : IO.Ref (Std.HashMap Step SetPathNodesId)
  owners_table    : IO.Ref (Std.HashMap PathNodeId SetPathNodesId)
  owners_set      : IO.Ref SetPathNodesId
  nodes_to_remove : IO.Ref SetPathNodesId
  current_step    : IO.Ref Step
  map_parent_id   : IO.Ref (Option NodeId)
  review_owners   : IO.Ref Bool
  is_valid        : IO.Ref Bool
  kind_nodes_step : IO.Ref (Std.HashMap Step String)

namespace GPow

def new : IO GPow := do
  let lines_table ← IO.mkRef {}
  let owners_table ← IO.mkRef {}
  let owners_set ← IO.mkRef {}
  let nodes_to_remove ← IO.mkRef {}
  let current_step ← IO.mkRef 0
  let map_parent_id ← IO.mkRef none
  let review_owners ← IO.mkRef false
  let is_valid ← IO.mkRef true
  let kind_nodes_step ← IO.mkRef {}

  pure {
    lines_table,
    owners_table,
    owners_set,
    nodes_to_remove,
    current_step,
    map_parent_id,
    review_owners,
    is_valid,
    kind_nodes_step
  }

def clone (gpow : GPow) : IO GPow := do
  let lines_table ← gpow.lines_table.get
  let owners_table ← gpow.owners_table.get
  let owners_set ← gpow.owners_set.get
  let nodes_to_remove ← gpow.nodes_to_remove.get
  let current_step ← gpow.current_step.get
  let map_parent_id ← gpow.map_parent_id.get
  let review_owners ← gpow.review_owners.get
  let is_valid ← gpow.is_valid.get
  let kind_nodes_step ← gpow.kind_nodes_step.get

  -- Value types being put into new Refs -> adequate deep copy for these types
  -- Std.HashMap/Set are persistent/value semantics in Lean (copy-on-write effectively)

  pure {
    lines_table := ← IO.mkRef lines_table,
    owners_table := ← IO.mkRef owners_table,
    owners_set := ← IO.mkRef owners_set,
    nodes_to_remove := ← IO.mkRef nodes_to_remove,
    current_step := ← IO.mkRef current_step,
    map_parent_id := ← IO.mkRef map_parent_id,
    review_owners := ← IO.mkRef review_owners,
    is_valid := ← IO.mkRef is_valid,
    kind_nodes_step := ← IO.mkRef kind_nodes_step
  }

end GPow

-- Placeholder helpers - Implementing logic from graph_pow_up.jl

def add_as_owner_of_all! (gpow : GPow) (path_id_node : PathNodeId) : IO Unit := do
  gpow.owners_table.modify fun table =>
    -- table maps PathNodeId -> SetPathNodesId
    -- for each (id, set) in table, insert path_id_node into set
    -- Since HashMap.mapVals is not strict IO, we can do it functionally
    table.fold (fun acc k v => acc.insert k (v.insert path_id_node)) {}

  gpow.owners_set.modify (·.insert path_id_node)

def add_node_set_owners! (gpow : GPow) (map_id_node : NodeId) : IO Unit := do
  let parent_id ← gpow.map_parent_id.get
  let path_id_node := AbsSat.Utils.Alias.new_path_id map_id_node parent_id
  let current_step ← gpow.current_step.get

  -- gpath.lines_table[gpath.current_step] = SetPathNodesId([path_id_node])
  gpow.lines_table.modify (fun t => t.insert current_step (({} : SetPathNodesId).insert path_id_node))

  -- gpath.owners_table[path_id_node] = deepcopy(gpath.owners_set)
  let owners_current ← gpow.owners_set.get
  gpow.owners_table.modify (fun t => t.insert path_id_node owners_current)

  add_as_owner_of_all! gpow path_id_node

def do_up! (gpow : GPow) (map_id_node : NodeId) (_title : String) : IO Unit := do
  let valid ← gpow.is_valid.get
  if valid then
    add_node_set_owners! gpow map_id_node
    gpow.current_step.modify (· + 1)
    gpow.map_parent_id.set (some map_id_node)

def filter! (gpow : GPow) (_requires : SetNodesId) : IO Unit := do
  -- TODO: Implement filter logic from graph_pow_filter.jl
  -- Currently just a stub
  pure ()

def do_up_filtering! (gpow : GPow) (requires : SetNodesId) (map_id_node : NodeId) (title : String) : IO Unit := do
  filter! gpow requires
  do_up! gpow map_id_node title

end AbsSat.GraphPow
