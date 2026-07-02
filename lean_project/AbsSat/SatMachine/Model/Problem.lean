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

-- Fold a sequence of per-layer choices onto a starting path, one at a
-- time, exactly the way `run_layers` processes layers left to right
-- (each choice's id is prepended, so the *last* choice ends up at the
-- head of `visited_nodes`).
def fold_choices (choices : List PureNode) (p : PurePath) : PurePath :=
  match choices with
  | [] => p
  | c :: cs => fold_choices cs { visited_nodes := c.id :: p.visited_nodes }

/--
  A witness that `layers` is solvable via a concrete sequence of
  per-layer choices: `choices[i]` comes from `layers[i]`, and its
  requirements are satisfiable using only the *earlier* choices
  (`prefix_path`, which accumulates exactly like `run_layers` does).

  This is the natural notion of solvability for a layered, causally
  ordered algorithm like this one: it is exactly what lets `run_pure`
  reconstruct the solution one layer at a time, and it is what
  `evolve_path_nodes`'s exhaustive filtering guarantees will be found.
-/
def ChoicesValid : List (List PureNode) → List PureNode → PurePath → Prop
  | [], [], _ => True
  | layer :: layers_rest, choice :: choices_rest, prefix_path =>
      choice ∈ layer ∧
      satisfies_requirements prefix_path choice.requirements = true ∧
      ChoicesValid layers_rest choices_rest { visited_nodes := choice.id :: prefix_path.visited_nodes }
  | _, _, _ => False

inductive Solvable (gmap : PureGMap) : Prop where
  | exists_choices (choices : List PureNode) :
      ChoicesValid gmap.layers choices { visited_nodes := [] } ->
      Solvable gmap

-- ============================================================
-- WELL-FORMEDNESS OF A GRAPH MAP
-- ============================================================

-- All nodes of a GMap, flattened across layers.
def PureGMap.all_nodes (gmap : PureGMap) : List PureNode :=
  gmap.layers.flatten

theorem mem_all_nodes {gmap : PureGMap} {layer : List PureNode} {n : PureNode}
    (hlayer : layer ∈ gmap.layers) (hn : n ∈ layer) : n ∈ gmap.all_nodes :=
  List.mem_flatten.mpr ⟨layer, hlayer, hn⟩

-- Every node in the head layer is tagged `k`, the next layer `k+1`, etc.
-- This mirrors the recursive structure of `run_layers` itself, so it
-- threads through that induction with no index arithmetic on `gmap.layers`.
def LayersLabeledFrom : List (List PureNode) → Nat → Prop
  | [], _ => True
  | layer :: rest, k => (∀ n ∈ layer, n.layer = k) ∧ LayersLabeledFrom rest (k + 1)

/--
  A GMap is well-formed when:
  1. `layers_labeled` — every node's `.layer` field honestly records the
     index of the layer list it belongs to (the layers are labeled
     consistently, as the real GraphMap construction guarantees).
  2. `unique_ids` — node ids are globally unique across the whole map.

  Together, these two conditions imply that two nodes from *different*
  layers can never share an id — this is the structural fact needed to
  eliminate `requirements_preservation` and `combine_requirements` as
  axioms.
-/
structure WellFormedGMap (gmap : PureGMap) : Prop where
  layers_labeled : LayersLabeledFrom gmap.layers 0
  unique_ids :
    ∀ n1 ∈ gmap.all_nodes, ∀ n2 ∈ gmap.all_nodes, n1.id = n2.id → n1 = n2

-- Decomposition lemmas: splitting a labeled list at `past ++ layers`
-- pushes the offset `k` forward by `past.length` for the remaining layers,
-- and bounds every node already consumed in `past` strictly below that offset.

theorem layers_labeled_drop (past layers : List (List PureNode)) (k : Nat) :
    LayersLabeledFrom (past ++ layers) k →
    LayersLabeledFrom layers (k + past.length) := by
  induction past generalizing k with
  | nil => simp
  | cons p ps ih =>
    intro h
    simp only [List.cons_append, LayersLabeledFrom] at h
    have := ih (k := k + 1) h.2
    have heq : k + 1 + ps.length = k + (p :: ps).length := by simp [List.length_cons]; omega
    rwa [heq] at this

theorem past_nodes_below (past layers : List (List PureNode)) (k : Nat) :
    LayersLabeledFrom (past ++ layers) k →
    ∀ layer ∈ past, ∀ n ∈ layer, n.layer < k + past.length := by
  induction past generalizing k with
  | nil => intro _ layer hlayer; cases hlayer
  | cons p ps ih =>
    intro h layer hlayer n hn
    simp only [List.cons_append, LayersLabeledFrom] at h
    rcases List.mem_cons.mp hlayer with rfl | hmem
    · have := h.1 n hn
      simp [List.length_cons]; omega
    · have := ih (k := k + 1) h.2 layer hmem n hn
      simp [List.length_cons] at this ⊢; omega

-- ============================================================
-- PATH CONFINEMENT
-- ============================================================

-- Every id visited so far traces back to some node in the layers
-- processed so far. This rules out a path "accidentally" containing an
-- id that belongs to a layer not yet processed.
def path_confined_to (layers : List (List PureNode)) (p : PurePath) : Prop :=
  ∀ id ∈ p.visited_nodes, ∃ layer ∈ layers, ∃ n ∈ layer, n.id = id

end AbsSat.SatMachine.Model
