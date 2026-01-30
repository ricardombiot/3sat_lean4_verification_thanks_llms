import Std

namespace AbsSat.Utils.Alias

structure NodeId where
  step  : Int
  index : Int
  deriving BEq, Hashable, Repr

def as_key (node_id : NodeId) : String :=
  s!"k{node_id.step}.{node_id.index}"

abbrev Step := Int
abbrev IndexNode := Int

abbrev SetNodesId := Std.HashSet NodeId

structure PathNodeId where
  id        : NodeId
  parent_id : Option NodeId
  deriving BEq, Hashable, Repr

instance : ToString NodeId where
  toString := as_key

abbrev SetPathNodesId := Std.HashSet PathNodeId

def new_path_id (id : NodeId) (parent_id : Option NodeId) : PathNodeId :=
  { id, parent_id }

-- as_key (node_id : Option NodeId) : String  REMAME as_key_from_nodeId
def as_key_from_nodeId (node_id : Option NodeId) : String :=
  match node_id with
  | some id => as_key id
  | none => "root"

def as_key_from_PathNodeId (path_node_id : PathNodeId) : String :=
  s!"{as_key path_node_id.id}__{as_key_from_nodeId path_node_id.parent_id}"

instance : ToString PathNodeId where
  toString := as_key_from_PathNodeId

instance : ToString SetPathNodesId where
  toString s :=
    let keys := s.toArray.map as_key_from_PathNodeId
    let sortedKeys := keys.qsort (· < ·)
    String.intercalate "\n" sortedKeys.toList

section Theorems

theorem as_key_format (step index : Int) :
  as_key { step := step, index := index } = s!"k{step}.{index}" := by
  rfl

theorem as_key_option_node_id :
  as_key_from_nodeId (none : Option NodeId) = "root" := by
  rfl

theorem as_key_path_node_id_none (id : NodeId) :
  as_key_from_PathNodeId { id, parent_id := none } = s!"{as_key id}__root" := by
  simp [as_key_from_PathNodeId, as_key_from_nodeId, as_key]
  rw [String.append_assoc]
  rfl

theorem as_key_path_node_id_some (id p : NodeId) :
  as_key_from_PathNodeId { id, parent_id := some p } = s!"{as_key id}__{as_key p}" := by
  simp [as_key_from_PathNodeId, as_key_from_nodeId, as_key]

theorem new_path_id_correct (id parent_id) :
  new_path_id id parent_id = { id, parent_id } := by
  rfl

end Theorems

section Examples

def run_tests : IO Unit := do
  let node1 := NodeId.mk 1 2
  let expected_key := "k1.2"
  let actual_key := as_key node1
  assert! actual_key == expected_key

  let node2 := NodeId.mk (-1) 0
  let expected_key2 := "k-1.0"
  let actual_key2 := as_key node2
  assert! actual_key2 == expected_key2

  -- Tests for PathNodeId
  let path_node_1 := PathNodeId.mk node1 (some node2)
  let expected_path_key_1 := "k1.2__k-1.0"
  let actual_path_key_1 := as_key_from_PathNodeId path_node_1
  assert! actual_path_key_1 == expected_path_key_1

  let path_node_2 := PathNodeId.mk node2 none
  let expected_path_key_2 := "k-1.0__root"
  let actual_path_key_2 := as_key_from_PathNodeId path_node_2
  assert! actual_path_key_2 == expected_path_key_2

  -- Tests for SetPathNodesId
  let mut path_set : SetPathNodesId := {}
  let path_node_3 := PathNodeId.mk (NodeId.mk 3 4) (some node1)
  path_set := path_set.insert path_node_1
  path_set := path_set.insert path_node_2
  path_set := path_set.insert path_node_3

  let expected_set_string := "k-1.0__root\nk1.2__k-1.0\nk3.4__k1.2"
  let actual_set_string := toString path_set
  assert! actual_set_string == expected_set_string

  -- Test for new_path_id
  let path_node_4 := new_path_id node1 (some node2)
  let expected_path_node_4 := PathNodeId.mk node1 (some node2)
  assert! path_node_4 == expected_path_node_4

  IO.println "All tests passed!"

#eval run_tests

end Examples

end AbsSat.Utils.Alias
