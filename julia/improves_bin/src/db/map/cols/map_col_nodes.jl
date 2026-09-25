module MapCollectionNodes
    using Main.AbsSat.Alias: Step, NodeId, IndexNode, SetNodesId
    using Main.AbsSat.DBDocuments.MapDocumentNode: MapDocNode

    mutable struct MapColNodesLine
        step :: Step
        table :: Dict{IndexNode, MapDocNode}
        node_ids :: SetNodesId
        count :: Int8
        is_valid :: Bool
    end

    function new(step :: Step) :: MapColNodesLine
        table = Dict{IndexNode, MapDocNode}()
        node_ids = SetNodesId()
        count = Int8(0)
        is_valid = true
        MapColNodesLine(step, table, node_ids, count, is_valid)
    end

    function get_node(col_nodes :: MapColNodesLine, id :: NodeId) :: Union{MapDocNode, Nothing}
        index = id.index

        if haskey(col_nodes.table, index)
            return col_nodes.table[index]
        else
            return nothing
        end
    end

    function push_node!(col_nodes :: MapColNodesLine, node :: MapDocNode)
        index = node.id.index
        col_nodes.table[index] = node
        col_nodes.count += 1
        push!(col_nodes.node_ids, node.id)
    end

end
