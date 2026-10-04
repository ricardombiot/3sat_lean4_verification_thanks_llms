module PathPowReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias

    using Main.AbsSat.GraphPow: GPow
    using Main.AbsSat.GraphPow

    mutable struct GPowReader
        gpath :: GPow
        solution :: BitArray{1}
        step :: Step
        last_selected :: Union{Nothing,PathNodeId}
        last_requires :: Union{Nothing,SetNodesId}
        is_finished :: Bool
    end

    function new(gpath :: GPow)
        solution = BitArray([])
        step = Step(0)
        last_selected = nothing
        last_requires = nothing
        is_finished = false

        GPowReader(gpath, solution, step, last_selected, last_requires, is_finished)
    end

    function read!(reader :: GPowReader)
        while !reader.is_finished
            read_step!(reader)
        end
    end

    function read_step!(reader :: GPowReader)
        if !reader.is_finished
            select_id!(reader)
            register_selection!(reader)
            filter_gpath!(reader)
            reader.step += 2
        end
    end

    function select_id!(reader :: GPowReader)
        ids = reader.gpath.lines_table[reader.step]

        #if isempty(ids)
        #    println("Ouch... $(reader.step)/ $(reader.gpath.current_step)")
        #end

        last_selected = first(ids)
        map_id_node = last_selected.id

        reader.last_selected = last_selected
        reader.last_requires = SetNodesId([map_id_node])
    end

    function register_selection!(reader :: GPowReader)
        node_id = reader.last_selected

        if GraphPow.is_kind_literal(reader.gpath, node_id)
            is_literal_value_zero = node_id.id.index == 0
            if is_literal_value_zero
                push!(reader.solution, 0)
            else
                push!(reader.solution, 1)
            end
        else
            # when is gate_or || fusion kind node
            reader.is_finished = true
        end
    end

    function filter_gpath!(reader :: GPowReader)
        if !reader.is_finished
            GraphPow.filter!(reader.gpath, reader.last_requires)

            if !reader.gpath.is_valid
                throw("GRAVE ERROR READER... GPATH INVALID.")
            end
        end
    end

end
