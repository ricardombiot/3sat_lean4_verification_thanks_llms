import Std.Data.HashSet
import AbsSat.Utils.Alias
import AbsSat.Db.Path.Docs.PathDocOwners

namespace AbsSat.Db.Path.Docs.PathDocNode

open AbsSat.Utils.Alias
open AbsSat.Db.Path.Docs.PathDocOwners

structure PathDocNode where
  id : PathNodeId
  title : String
  parents : Std.HashSet PathNodeId
  sons : Std.HashSet PathNodeId
  owners : PathDocOwners

namespace PathDocNode

def new (id : PathNodeId) (title : String) : PathDocNode :=
  {
    id := id,
    title := title,
    parents := {},
    sons := {},
    owners := PathDocOwners.insert PathDocOwners.new id
  }

instance : Inhabited PathDocNode := ⟨new { id := { step := 0, index := 0 }, parent_id := none } ""⟩

def is_root (node : PathDocNode) : Bool :=
  node.id.parent_id.isNone

def get_step (node : PathDocNode) : Int :=
  node.id.id.step

def addSon (node : PathDocNode) (id : PathNodeId) : PathDocNode :=
  { node with sons := node.sons.insert id }

def addParent (node : PathDocNode) (id : PathNodeId) : PathDocNode :=
  { node with parents := node.parents.insert id }

def removeSon (node : PathDocNode) (id : PathNodeId) : PathDocNode :=
  { node with sons := node.sons.erase id }

def removeParent (node : PathDocNode) (id : PathNodeId) : PathDocNode :=
  { node with parents := node.parents.erase id }

def putOwners (node : PathDocNode) (owners : PathDocOwners) : PathDocNode :=
  { node with owners := owners }

def addOwner (node : PathDocNode) (id : PathNodeId) : PathDocNode :=
  { node with owners := PathDocOwners.insert node.owners id }

def removeOwner (node : PathDocNode) (id : PathNodeId) : PathDocNode :=
  { node with owners := PathDocOwners.remove node.owners id }

def link (node_parent : PathDocNode) (node_son : PathDocNode) : (PathDocNode × PathDocNode) :=
  (addSon node_parent node_son.id, addParent node_son node_parent.id)

def unionSets {α : Type} [BEq α] [Hashable α] (s1 s2 : Std.HashSet α) : Std.HashSet α :=
  s2.fold (fun s item => s.insert item) s1

def union (node_a : PathDocNode) (node_b : PathDocNode) : PathDocNode :=
  let new_parents := unionSets node_a.parents node_b.parents
  let new_sons := unionSets node_a.sons node_b.sons
  let new_owners := PathDocOwners.union node_a.owners node_b.owners
  { node_a with
    parents := new_parents,
    sons := new_sons,
    owners := new_owners
  }

def is_valid (node : PathDocNode) : Bool :=
  PathDocOwners.isValid node.owners

-- Helper functions for assertions (previously marked as theorems)
def check_new_properties (id : PathNodeId) (title : String) : Bool :=
  let node := new id title
  node.id == id &&
  node.title == title &&
  node.parents.isEmpty &&
  node.sons.isEmpty &&
  PathDocOwners.isOwner node.owners id

def check_is_root_correctness : Bool :=
  let rootId : PathNodeId := { id := { step := 0, index := 0 }, parent_id := none }
  let childId : PathNodeId := { id := { step := 1, index := 0 }, parent_id := some rootId.id }
  let rootNode := new rootId "root"
  let childNode := new childId "child"
  rootNode.is_root && !childNode.is_root

def check_get_step_correctness : Bool :=
  let nodeId : PathNodeId := { id := { step := 42, index := 0 }, parent_id := none }
  let node := new nodeId "test"
  get_step node == 42

def check_is_valid_correctness : Bool :=
  let nodeId : PathNodeId := { id := { step := 0, index := 0 }, parent_id := none }
  let node := new nodeId "test"
  let validNode := node
  let invalidOwners := { node.owners with valid := false }
  let invalidNode := { node with owners := invalidOwners }
  is_valid validNode && !is_valid invalidNode

end PathDocNode

-- Examples and Tests
section Examples
 open PathDocNode

  def run_tests : IO Unit := do
    let rootId : PathNodeId := { id := { step := 0, index := 0 }, parent_id := none }
    let childId : PathNodeId := { id := { step := 1, index := 0 }, parent_id := some rootId.id }

    -- Verify properties
    assert! (check_new_properties rootId "root")
    assert! (check_new_properties childId "child")
    assert! check_is_root_correctness
    assert! check_get_step_correctness
    assert! check_is_valid_correctness

    IO.println "All PathDocNode tests passed!"

  -- Run tests (commented out due to internal sorries if any check hits them, but checks seem safe as they use safe functions)
  #eval run_tests

end Examples

end AbsSat.Db.Path.Docs.PathDocNode
