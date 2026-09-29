module PathDocumentNode
    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId
    using Main.AbsSat.Undo

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

    # Toda modificación de los enlaces pasa por aquí (para poder deshacerla).
    function add_link!(set :: SetPathNodesId, id :: PathNodeId)
        if !(id in set)
            push!(set, id)
            Undo.active() && Undo.record!(() -> delete!(set, id))
        end
    end

    function delete_link!(set :: SetPathNodesId, id :: PathNodeId)
        if id in set
            delete!(set, id)
            Undo.active() && Undo.record!(() -> push!(set, id))
        end
    end

    add_son!(node :: PathDocNode, id :: PathNodeId) = add_link!(node.sons, id)
    add_parent!(node :: PathDocNode, id :: PathNodeId) = add_link!(node.parents, id)
    remove_son!(node :: PathDocNode, id :: PathNodeId) = delete_link!(node.sons, id)
    remove_parent!(node :: PathDocNode, id :: PathNodeId) = delete_link!(node.parents, id)

    function link!(node_parent :: PathDocNode, node_son :: PathDocNode)
        add_parent!(node_son, node_parent.id)
        add_son!(node_parent, node_son.id)
    end

    # Copia por estructura: los ids y el título son inmutables, solo se copian los conjuntos.
    copy_node(node :: PathDocNode) :: PathDocNode = PathDocNode(node.id, node.title, copy(node.parents), copy(node.sons))

    Base.deepcopy_internal(node :: PathDocNode, stackdict :: IdDict) = get!(() -> copy_node(node), stackdict, node)

    function union!(node :: PathDocNode, node_b :: PathDocNode)
        if node.id == node_b.id
            Base.union!(node.parents, node_b.parents)
            Base.union!(node.sons, node_b.sons)
        end
    end

end
