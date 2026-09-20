module Alias

    const Step = Int64
    const IndexNode = Int64

    const NodeId = NamedTuple{(:step, :index),Tuple{Step, IndexNode}}
    function as_key(node_id :: NodeId) :: String
        return "k$(node_id.step).$(node_id.index)"
    end
    const SetNodesId = Set{NodeId}

    const NodeIdOrNothing = Union{NodeId, Nothing}
    const PathNodeId = NamedTuple{(:id, :parent_id),Tuple{NodeId, NodeIdOrNothing}}
    const SetPathNodesId = Set{PathNodeId}

    function new_path_id(id :: NodeId, parent_id :: NodeIdOrNothing) :: PathNodeId
        path_node_id :: PathNodeId = (id=id, parent_id=parent_id)
        return path_node_id
    end

    function as_key(path_node_id :: PathNodeId) :: String
        id = as_key(path_node_id.id)
        parent_id = as_key(path_node_id.parent_id)
        return "$(id)__$(parent_id)"
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
