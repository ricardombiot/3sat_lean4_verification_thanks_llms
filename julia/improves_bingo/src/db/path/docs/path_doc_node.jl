module PathDocumentNode
    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId

    # Los owners ya no viven en el nodo: son las aristas del grafo de owners del gpath
    # (PathOwnersGraph, plan docs/plans/graph_owners.md). El nodo guarda solo la estructura.
    mutable struct PathDocNode
        id :: PathNodeId
        title :: String

        parents :: SetPathNodesId
        sons :: SetPathNodesId
    end

    function new(id :: PathNodeId, title :: String) :: PathDocNode
        return PathDocNode(id, title, SetPathNodesId(), SetPathNodesId())
    end

    function is_root(node :: PathDocNode) :: Bool
        return node.id.parent_id == nothing
    end

    function get_step(node :: PathDocNode) :: Step
        return node.id.id.step
    end

    function add_son!(node :: PathDocNode, id :: PathNodeId)
        push!(node.sons, id)
    end

    function add_parent!(node :: PathDocNode, id :: PathNodeId)
        push!(node.parents, id)
    end

    function remove_son!(node :: PathDocNode, id :: PathNodeId)
        delete!(node.sons, id)
    end

    function remove_parent!(node :: PathDocNode, id :: PathNodeId)
        delete!(node.parents, id)
    end

    function link!(node_parent :: PathDocNode, node_son :: PathDocNode)
        add_parent!(node_son, node_parent.id)
        add_son!(node_parent, node_son.id)
    end

    function union!(node :: PathDocNode, node_b :: PathDocNode)
        if node.id == node_b.id
            Base.union!(node.parents, node_b.parents)
            Base.union!(node.sons, node_b.sons)
        end
    end

end
