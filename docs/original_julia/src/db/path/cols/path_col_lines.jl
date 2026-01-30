module PathCollectionLines
    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId

    using Main.AbsSat.DBDocuments.PathDocumentNode: PathDocNode
    using Main.AbsSat.DBCollections.PathCollectionNodes: PathColNodesLine

    using Main.AbsSat.DBCollections.PathCollectionNodes
    using Main.AbsSat.DBDocuments.PathDocumentNode

    mutable struct PathColLines
        table :: Dict{Step, PathColNodesLine}
        is_valid :: Bool
    end

    function new()
        table = Dict{Step, PathColNodesLine}()
        is_valid = true
        PathColLines(table, is_valid)
    end

    function union!(col_lines :: PathColLines, col_lines_b :: PathColLines)
        #! [for] $ O(S) $
        for (step, col_nodes_b) in col_lines_b.table
            col_nodes = get_step(col_lines, step)

            if col_nodes != nothing
                PathCollectionNodes.union!(col_nodes, col_nodes_b)
            else
                col_lines.table[step] = deepcopy(col_nodes_b)
            end
        end
    end

    function for_each(col_lines :: PathColLines, fn_each)
        #! [for] $ O(S) $
        for (step, col_nodes) in col_lines.table
            PathCollectionNodes.for_each(col_nodes, fn_each)
        end
    end

    function filter!(col_lines :: PathColLines, fn_filter)
        #! [for] $ O(S) $
        for (step, col_nodes) in col_lines.table
            PathCollectionNodes.filter!(col_nodes, fn_filter)
            check_if_valid_line!(col_lines, step)

            if !col_lines.is_valid
                break
            end
        end
    end

    function for_each_on_step(col_lines :: PathColLines, step :: Step, fn_each)
        col_nodes = get_step(col_lines, step)

        if col_nodes != nothing
            PathCollectionNodes.for_each(col_nodes, fn_each)
        else
            println("Dont found $step...")
        end
    end

    function get_step(col_lines :: PathColLines, step :: Step) :: Union{PathColNodesLine, Nothing}
        if haskey(col_lines.table, step)
            return col_lines.table[step]
        else
            return nothing
        end
    end

    function get_ids_step(col_lines :: PathColLines, step :: Step) :: SetPathNodesId
        line = get_step(col_lines, step)
        if line != nothing
            return line.node_ids
        else
            return SetPathNodesId()
        end
    end

    function link_nodes!(col_lines :: PathColLines, id_parent :: PathNodeId,  id_son :: PathNodeId)
        node_parent = get_node(col_lines, id_parent)
        node_son = get_node(col_lines, id_son)

        PathDocumentNode.link!(node_parent, node_son)
    end

    function get_node(col_lines :: PathColLines, id :: PathNodeId) :: Union{PathDocNode, Nothing}
        line = get_step(col_lines, id.id.step)

        if line != nothing
            return PathCollectionNodes.get_node(line, id)
        end

        return nothing
    end

    function push_node!(col_lines :: PathColLines, node :: PathDocNode)
        step = node.id.id.step

        if !haskey(col_lines.table, step)
            col_lines.table[step] = PathCollectionNodes.new(step)
        end

        PathCollectionNodes.push_node!(col_lines.table[step], node)
    end


    function remove_node!(col_lines :: PathColLines, id :: PathNodeId)
        line = get_step(col_lines, id.id.step)
        PathCollectionNodes.remove_node!(line, id)

        check_if_valid_line!(col_lines, step)
    end

    function check_if_valid_line!(col_lines :: PathColLines, step :: Step)
        line = get_step(col_lines, step)

        if PathCollectionNodes.is_empty(line)
            col_lines.is_valid = false
        end
    end


end
