module MapCollectionLines
    using Main.AbsSat.Alias: Step, NodeId, SetNodesId

    using Main.AbsSat.DBDocuments.MapDocumentNode: MapDocNode
    using Main.AbsSat.DBCollections.MapCollectionNodes: MapColNodesLine

    using Main.AbsSat.DBCollections.MapCollectionNodes
    using Main.AbsSat.DBDocuments.MapDocumentNode

    mutable struct MapColLines
        table :: Dict{Step, MapColNodesLine}
        is_valid :: Bool
    end

    function new()
        table = Dict{Step, MapColNodesLine}()
        is_valid = true
        MapColLines(table, is_valid)
    end

    function get_step(col_lines :: MapColLines, step :: Step) :: Union{MapColNodesLine, Nothing}
        if haskey(col_lines.table, step)
            return col_lines.table[step]
        else
            return nothing
        end
    end

    function get_ids_step(col_lines :: MapColLines, step :: Step) :: SetNodesId
        line = get_step(col_lines, step)
        if line != nothing
            return line.node_ids
        else
            return SetNodesId()
        end
    end

    function link_nodes!(col_lines :: MapColLines, id_parent :: NodeId,  id_son :: NodeId)
        node_parent = get_node(col_lines, id_parent)
        node_son = get_node(col_lines, id_son)

        MapDocumentNode.add_parent!(node_son, id_parent)
        MapDocumentNode.add_son!(node_parent, id_son)
    end

    function get_node(col_lines :: MapColLines, id :: NodeId) :: Union{MapDocNode, Nothing}
        line = get_step(col_lines, id.step)

        if line != nothing
            return MapCollectionNodes.get_node(line, id)
        end

        return nothing
    end

    function push_node!(col_lines :: MapColLines, node :: MapDocNode)
        step = node.id.step

        if !haskey(col_lines.table, step)
            col_lines.table[step] = MapCollectionNodes.new(step)
        end

        MapCollectionNodes.push_node!(col_lines.table[step], node)
    end




end
