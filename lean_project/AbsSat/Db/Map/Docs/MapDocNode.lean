import AbsSat.Utils.Alias
import Std.Data.HashSet

namespace AbsSat.Db.Map.Docs.MapDocNode

open Utils.Alias

structure MapDocNode where
  id : NodeId
  title : String
  parents : SetNodesId
  sons : SetNodesId
  requires : SetNodesId
deriving Repr

instance : BEq MapDocNode where
  beq a b :=
    a.id == b.id &&
    a.title == b.title &&
    a.parents.toList.length == b.parents.toList.length &&
    -- Simplified set equality for now since sorting requires Ord/LE which might be complex
    -- For now, just check size and ID structure if needed, or assume if ID is same, node is same?
    -- No, this is a value object.
    -- Better: implement set equality helper.
    (a.parents.toList.all (b.parents.contains ·)) &&
    (a.sons.toList.all (b.sons.contains ·)) &&
    (a.requires.toList.all (b.requires.contains ·))

def new (id : NodeId) (title : String) : MapDocNode :=
  {
    id := id,
    title := title,
    parents := {},
    sons := {},
    requires := {}
  }

def add_son! (node : MapDocNode) (id : NodeId) : MapDocNode :=
  { node with sons := node.sons.insert id }

def add_parent! (node : MapDocNode) (id : NodeId) : MapDocNode :=
  { node with parents := node.parents.insert id }

def add_require! (node : MapDocNode) (id : NodeId) : MapDocNode :=
  { node with requires := node.requires.insert id }

end AbsSat.Db.Map.Docs.MapDocNode
