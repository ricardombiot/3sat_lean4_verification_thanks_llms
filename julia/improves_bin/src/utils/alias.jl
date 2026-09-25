module Alias

    const Step = Int64
    const IndexNode = Int64

    const NodeId = NamedTuple{(:step, :index),Tuple{Step, IndexNode}}
    function as_key(node_id :: NodeId) :: String
        return "k$(node_id.step).$(node_id.index)"
    end
    const SetNodesId = Set{NodeId}

    const NodeIdOrNothing = Union{NodeId, Nothing}

    # Number of map ids that identify a path node: 2 = (parent, id), 3 = (grandparent, parent, id).
    # With 2 the grandparent is always nothing, which is the identifier the machine used before the window.
    const WINDOW = Ref{Int}(3)

    # A struct and not a NamedTuple: hashing a NamedTuple with nested Unions is ~15x slower,
    # and these identifiers are the keys of every Dict and Set of the machine.
    struct PathNodeId
        gparent_id :: NodeIdOrNothing
        parent_id :: NodeIdOrNothing
        id :: NodeId
    end
    const SetPathNodesId = Set{PathNodeId}

    @inline hash_node_id(node_id :: NodeId, h :: UInt) :: UInt = hash(node_id.step, hash(node_id.index, h))
    @inline hash_node_id(node_id :: Nothing, h :: UInt) :: UInt = hash(-1, h)
    function Base.hash(path_node_id :: PathNodeId, h :: UInt) :: UInt
        h = hash_node_id(path_node_id.gparent_id, h)
        h = hash_node_id(path_node_id.parent_id, h)
        return hash_node_id(path_node_id.id, h)
    end

    # Window of two ids. GraphPow builds its identifiers with this one, whatever WINDOW says.
    function new_path_id(id :: NodeId, parent_id :: NodeIdOrNothing) :: PathNodeId
        return PathNodeId(nothing, parent_id, id)
    end

    function root_path_id(id :: NodeId) :: PathNodeId
        return new_path_id(id, nothing)
    end

    # Shift of the window: (gp, p, last) + id -> (p, last, id)
    function shift_path_id(last :: PathNodeId, id :: NodeId) :: PathNodeId
        gparent_id = WINDOW[] >= 3 ? last.parent_id : nothing
        return PathNodeId(gparent_id, last.id, id)
    end

    function as_key(path_node_id :: PathNodeId) :: String
        id = as_key(path_node_id.id)
        parent_id = as_key(path_node_id.parent_id)
        if path_node_id.gparent_id === nothing
            return "$(id)__$(parent_id)"
        else
            gparent_id = as_key(path_node_id.gparent_id)
            return "$(id)__$(parent_id)__$(gparent_id)"
        end
    end

    function as_key(path_node_id :: Nothing) :: String
        return "root"
    end

    function to_string(path_node_id :: PathNodeId) :: String
        return as_key(path_node_id)
    end

    function to_string(set :: SetPathNodesId) :: String
        result = ""
        for path_node_id in set
            result *= as_key(path_node_id)
            result *= "\n"
        end

        return result
    end
end
