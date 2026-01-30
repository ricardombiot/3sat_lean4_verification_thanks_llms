module MapDocumentNode
    using Main.AbsSat.Alias: NodeId, SetNodesId

    mutable struct MapDocNode
        id :: NodeId
        title :: String

        parents :: SetNodesId
        sons :: SetNodesId
        requires :: SetNodesId
    end

    function new(id :: NodeId, title :: String) :: MapDocNode
        parents = SetNodesId()
        sons = SetNodesId()
        requires = SetNodesId()

        MapDocNode(id, title, parents, sons, requires)
    end

    function add_son!(node :: MapDocNode, id :: NodeId)
        push!(node.sons, id)
    end

    function add_parent!(node :: MapDocNode, id :: NodeId)
        push!(node.parents, id)
    end

    function add_require!(node :: MapDocNode, id :: NodeId)
        push!(node.requires, id)
    end
end
