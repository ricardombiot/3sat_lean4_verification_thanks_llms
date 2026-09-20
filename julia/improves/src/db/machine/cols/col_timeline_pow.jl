module CollectionTimelinePow
    using Main.AbsSat.Alias: Step, NodeId, PathNodeId, SetPathNodesId

    using Main.AbsSat.DBMachine.CollectionTimelinePowStep: ColTimelinePowStep
    using Main.AbsSat.DBMachine.CollectionTimelinePowStep
    using Main.AbsSat.GraphPow: GPow
    using Main.AbsSat.GraphPow

    mutable struct ColTimelinePow
        table :: Dict{Step, ColTimelinePowStep}
    end

    function new()
        table = Dict{Step, ColTimelinePowStep}()
        ColTimelinePow(table)
    end

    function init_gpath_seed!(timeline :: ColTimelinePow, node_id :: NodeId, title :: String)
        gpath = GraphPow.new()
        GraphPow.do_up!(gpath, node_id)
        timeline_step = get_if_dontexiste_create_it!(timeline, Step(0))
        CollectionTimelinePowStep.impact!(timeline_step, gpath)
    end

    function get_counter_graphs_step(timeline :: ColTimelinePow, step :: Step) :: Int8
        timeline_step = get_step(timeline, step)

        if timeline_step == nothing
            return Int8(0)
        else
            return timeline_step.counter_graphs
        end
    end

    function remove_line!(timeline :: ColTimelinePow, step :: Step)
        delete!(timeline.table, step)
    end

    function get_step(timeline :: ColTimelinePow, step :: Step) :: Union{ColTimelinePowStep, Nothing}
        if haskey(timeline.table, step)
            return timeline.table[step]
        else
            return nothing
        end
    end

    function get_gpath!(timeline :: ColTimelinePow, step :: Step, map_node_id :: NodeId) :: Union{GPow,Nothing}
        timeline_step = get_step(timeline, step)

        if timeline_step != nothing
            return CollectionTimelinePowStep.get_gpath!(timeline_step, map_node_id)
        else
            return nothing
        end
    end

    function get_if_dontexiste_create_it!(timeline :: ColTimelinePow, step :: Step) :: ColTimelinePowStep
        timeline_step = get_step(timeline, step)

        if timeline_step == nothing
            timeline.table[step] = CollectionTimelinePowStep.new()
        end

        return timeline.table[step]
    end

    function for_each_gpath(timeline :: ColTimelinePow, step :: Step, fn_each)
        timeline_step = get_step(timeline, step)

        if timeline_step != nothing
            CollectionTimelinePowStep.for_each_gpath(timeline_step, fn_each)
        end
    end

    function impact!(timeline :: ColTimelinePow, step :: Step, gpath :: GPow)
        timeline_step = get_if_dontexiste_create_it!(timeline, step)

        if timeline_step != nothing
            CollectionTimelinePowStep.impact!(timeline_step, gpath)
        end
    end


end
