module PathDocumentNode
    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBDocuments.PathDocumentOwners: PathDocOwners
    using Main.AbsSat.DBDocuments.PathDocumentOwners

    mutable struct PathDocNode
        id :: PathNodeId
        title :: String

        parents :: SetPathNodesId
        sons :: SetPathNodesId
        owners :: PathDocOwners
    end

    function new(id :: PathNodeId, title :: String) :: PathDocNode
        parents = SetPathNodesId()
        sons = SetPathNodesId()
        owners = PathDocumentOwners.new()

        node = PathDocNode(id, title, parents, sons, owners)
        add_owner!(node, id)

        return node
    end

    function is_root(node :: PathDocNode) :: Bool
        return node.id.parent_id == nothing
    end

    function get_step(node :: PathDocNode) :: Step
        return node.id.id.step
    end

    function add_son!(node :: PathDocNode, id :: PathNodeId)
        push!(node.sons, id)
        add_owner!(node, id)
    end

    function add_parent!(node :: PathDocNode, id :: PathNodeId)
        push!(node.parents, id)
        add_owner!(node, id)
    end

    function remove_son!(node :: PathDocNode, id :: PathNodeId)
        delete!(node.sons, id)
        remove_owner!(node, id)
    end

    function remove_parent!(node :: PathDocNode, id :: PathNodeId)
        delete!(node.parents, id)
        remove_owner!(node, id)
    end

    function link!(node_parent :: PathDocNode, node_son :: PathDocNode)
        add_parent!(node_son, node_parent.id)
        add_son!(node_parent, node_son.id)
    end

    function put_owners!(node :: PathDocNode, owners_inmutable :: PathDocOwners)
        node.owners = deepcopy(owners_inmutable)
    end

    function add_owner!(node :: PathDocNode, id :: PathNodeId)
        PathDocumentOwners.insert!(node.owners, id)
    end

    function remove_owner!(node :: PathDocNode, id :: PathNodeId)
        PathDocumentOwners.remove!(node.owners, id)
    end

    function is_valid(node :: PathDocNode) :: Bool
        PathDocumentOwners.is_valid(node.owners)
    end

    function union!(node :: PathDocNode, node_b :: PathDocNode)
        if node.id == node_b.id

            Base.union!(node.parents, node_b.parents)
            Base.union!(node.sons, node_b.sons)
            PathDocumentOwners.union!(node.owners, node_b.owners)
        end
    end

end
