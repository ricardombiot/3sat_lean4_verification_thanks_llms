module PathCollectionNodes
    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBDocuments.PathDocumentNode: PathDocNode
    using Main.AbsSat.DBDocuments.PathDocumentNode

    mutable struct PathColNodesLine
        step :: Step
        table :: Dict{PathNodeId, PathDocNode}
        node_ids :: SetPathNodesId
        count :: Int8
        is_valid :: Bool
    end

    function new(step :: Step) :: PathColNodesLine
        table = Dict{PathNodeId, PathDocNode}()
        node_ids = SetPathNodesId()
        count = Int8(0)
        is_valid = true
        PathColNodesLine(step, table, node_ids, count, is_valid)
    end

    function union!(col_nodes :: PathColNodesLine, col_nodes_b :: PathColNodesLine)
        #! [for] $ O(7*7) $
        for (path_node_id, node_b) in col_nodes_b.table
            node = get_node(col_nodes, path_node_id)

            if node != nothing
                PathDocumentNode.union!(node, node_b)
            else
                node_copy = deepcopy(node_b)
                push_node!(col_nodes, node_copy)
            end
        end
    end

    function for_each(col_nodes :: PathColNodesLine, fn_each)
        #! [for] $ O(7*7) $
        for (path_node_id, node) in col_nodes.table
            fn_each(node)
        end
    end

    function filter!(col_nodes :: PathColNodesLine, fn_filter) #::  Array{PathNodeId,1}
        #list_ids_to_remove = Array{PathNodeId, 1}()

        #! [for] $ O(7*7) $
        for (path_node_id, node) in col_nodes.table
            if fn_filter(node)
                remove_node!(col_nodes, path_node_id)
            end
        end

        #return list_ids_to_remove
    end

    function get_node(col_nodes :: PathColNodesLine, id :: PathNodeId) :: Union{PathDocNode, Nothing}
        if haskey(col_nodes.table, id)
            return col_nodes.table[id]
        else
            return nothing
        end
    end

    function push_node!(col_nodes :: PathColNodesLine, node :: PathDocNode)
        col_nodes.table[node.id] = node
        col_nodes.count += 1
        push!(col_nodes.node_ids, node.id)
    end

    function remove_node!(col_nodes :: PathColNodesLine, id :: PathNodeId)
        if haskey(col_nodes.table, id)
            delete!(col_nodes.table, id)
            delete!(col_nodes.node_ids, id)
            col_nodes.count -= 1
        end
    end

    function is_empty(col_nodes :: PathColNodesLine) :: Bool
        return col_nodes.count == 0
    end

end
