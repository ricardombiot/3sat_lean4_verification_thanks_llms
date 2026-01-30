import AbsSat.SatMachine.Model.PureSatMachine

namespace AbsSat.SatMachine.Model

open AbsSat.SatMachine.Model

-- Helpers
def list_contains {α} [BEq α] (l : List α) (x : α) : Bool :=
  List.any l (fun y => y == x)

-- Check if path contains a node from specific layer
def layer_covered (nodes : List PureNode) (path : PurePath) : Bool :=
  nodes.any (fun n => list_contains path.visited_nodes n.id)

-- Recursive check for coverage
def all_layers_covered (layers : List (List PureNode)) (path : PurePath) : Bool :=
  match layers with
  | [] => true
  | nodes :: rest => layer_covered nodes path && all_layers_covered rest path

-- Check if all visited nodes in gmap have requirements met
-- Note: We iterate over all nodes in gmap to check if they are in path and if so, are satisfied.
def all_requirements_met (gmap : PureGMap) (path : PurePath) : Bool :=
  let all_nodes := List.foldl List.append [] gmap.layers
  all_nodes.all (fun n =>
    if list_contains path.visited_nodes n.id then
       satisfies_requirements path n.requirements
    else
       true
  )

def is_valid_solution (gmap : PureGMap) (path : PurePath) : Bool :=
  all_layers_covered gmap.layers path && all_requirements_met gmap path

inductive Solvable (gmap : PureGMap) : Prop where
  | exists_path (p : PurePath) :
      is_valid_solution gmap p = true ->
      Solvable gmap

end AbsSat.SatMachine.Model
