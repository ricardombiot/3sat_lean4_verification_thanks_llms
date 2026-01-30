module PathReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBDocuments.PathDocumentNode: PathDocNode
    using Main.AbsSat.DBDocuments.PathDocumentOwners: PathDocOwners
    using Main.AbsSat.DBCollections.PathCollectionNodes: PathColNodesLine
    using Main.AbsSat.DBCollections.PathCollectionLines: PathColLines


    using Main.AbsSat.Alias
    using Main.AbsSat.DBDocuments.PathDocumentNode
    using Main.AbsSat.DBDocuments.PathDocumentOwners
    using Main.AbsSat.DBCollections.PathCollectionNodes
    using Main.AbsSat.DBCollections.PathCollectionLines

    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    mutable struct GPathReader
        gpath :: GPath
        solution :: BitArray{1}
        step :: Step
        last_selected :: Union{Nothing,PathNodeId}
        last_requires :: Union{Nothing,SetNodesId}
        is_finished :: Bool
    end

    function new(gpath :: GPath)
        solution = BitArray([])
        step = Step(0)
        last_selected = nothing
        last_requires = nothing
        is_finished = false

        GPathReader(gpath, solution, step, last_selected, last_requires, is_finished)
    end

    function read!(reader :: GPathReader)
        # Only will iterate
        #! [while] $ O(L) $
        while !reader.is_finished
            read_step!(reader)
        end
    end

    function read_step!(reader :: GPathReader)
        if !reader.is_finished
            select_id!(reader)
            register_selection!(reader)
            filter_gpath!(reader)
            reader.step += 2
        end
    end

    function select_id!(reader :: GPathReader)
        ids = PathCollectionLines.get_ids_step(reader.gpath.table_lines, reader.step)

        #if isempty(ids)
        #    println("Ouch... $(reader.step)/ $(reader.gpath.current_step)")
        #end

        last_selected = first(ids)
        map_id_node = last_selected.id

        reader.last_selected = last_selected
        reader.last_requires = SetNodesId([map_id_node])
    end

    function register_selection!(reader :: GPathReader)
        path_node = PathCollectionLines.get_node(reader.gpath.table_lines, reader.last_selected)

        is_or = contains(path_node.title, "or")
        is_fusion = contains(path_node.title, "FusionNode")
        if is_or || is_fusion
            # Final of literals block
            reader.is_finished = true
        else
            literal_value = path_node.id.id.index
            push!(reader.solution, literal_value)
            #=
            is_literal_value_zero = path_node.id.id.index == 0
            if is_literal_value_zero
                push!(reader.solution, 0)
            else
                push!(reader.solution, 1)
            end
            =#
        end
    end

    function filter_gpath!(reader :: GPathReader)
        if !reader.is_finished
            GraphPath.filter!(reader.gpath, reader.last_requires)

            if !reader.gpath.is_valid
                throw("GRAVE ERROR READER... GPATH INVALID.")
            end
        end
    end

end
