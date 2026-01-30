namespace AbsSat.SatMachine.Model

-- Data Types equivalent to MapDocNode but pure (no IO, simplified)

structure Requirement where
  nodeId : Nat
  positive : Bool
  deriving Repr, BEq, Inhabited

structure PureNode where
  id : Nat
  layer : Nat
  requirements : List Requirement
  deriving Repr, BEq, Inhabited

structure PureGMap where
  layers : List (List PureNode)
  deriving Repr, Inhabited

structure PurePath where
  visited_nodes : List Nat
  deriving Repr, BEq, Inhabited

-- Helpers
def list_bind {α β} (l : List α) (f : α → List β) : List β :=
  match l with
  | [] => []
  | x :: xs => (f x) ++ (list_bind xs f)

-- Helper: Check if a set of requirements is met by the path
def satisfies_requirements (path : PurePath) (reqs : List Requirement) : Bool :=
  List.all reqs (fun req => List.any path.visited_nodes (fun id => id == req.nodeId))

-- Evolve path on a specific set of nodes (a layer)
def evolve_path_nodes (nodes : List PureNode) (path : PurePath) : List PurePath :=
  let candidates := List.filter (fun n => satisfies_requirements path n.requirements) nodes
  List.map (fun n => { visited_nodes := n.id :: path.visited_nodes }) candidates

def run_step_nodes (nodes : List PureNode) (paths : List PurePath) : List PurePath :=
  list_bind paths (fun p => evolve_path_nodes nodes p)

-- Structural recursion on layers
def run_layers (layers : List (List PureNode)) (current_paths : List PurePath) : List PurePath :=
  match layers with
  | [] => current_paths
  | nodes :: rest =>
    let next_paths := run_step_nodes nodes current_paths
    if next_paths.isEmpty then [] else run_layers rest next_paths

-- The main "run" function
def run_pure (gmap : PureGMap) : List PurePath :=
  run_layers gmap.layers [{ visited_nodes := [] }]

end AbsSat.SatMachine.Model
