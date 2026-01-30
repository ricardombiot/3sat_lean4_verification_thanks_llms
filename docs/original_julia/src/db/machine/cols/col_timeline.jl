module CollectionTimeline
    using Main.AbsSat.Alias: Step, NodeId, PathNodeId, SetPathNodesId

    using Main.AbsSat.DBMachine.CollectionTimelineStep: ColTimelineStep
    using Main.AbsSat.DBMachine.CollectionTimelineStep
    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    mutable struct ColTimeline
        table :: Dict{Step, ColTimelineStep}
    end

    function new()
        table = Dict{Step, ColTimelineStep}()
        ColTimeline(table)
    end

    function init_gpath_seed!(timeline :: ColTimeline, node_id :: NodeId, title :: String)
        gpath = GraphPath.new()
        GraphPath.do_up!(gpath, node_id, title)
        timeline_step = get_if_dontexiste_create_it!(timeline, Step(0))
        CollectionTimelineStep.impact!(timeline_step, gpath)
    end

    function get_counter_graphs_step(timeline :: ColTimeline, step :: Step) :: Int8
        timeline_step = get_step(timeline, step)

        if timeline_step == nothing
            return Int8(0)
        else
            return timeline_step.counter_graphs
        end
    end

    function remove_line!(timeline :: ColTimeline, step :: Step)
        delete!(timeline.table, step)
    end

    function get_step(timeline :: ColTimeline, step :: Step) :: Union{ColTimelineStep, Nothing}
        if haskey(timeline.table, step)
            return timeline.table[step]
        else
            return nothing
        end
    end

    function get_gpath!(timeline :: ColTimeline, step :: Step, map_node_id :: NodeId) :: Union{GPath,Nothing}
        timeline_step = get_step(timeline, step)

        if timeline_step != nothing
            return CollectionTimelineStep.get_gpath!(timeline_step, map_node_id)
        else
            return nothing
        end
    end

    function get_if_dontexiste_create_it!(timeline :: ColTimeline, step :: Step) :: ColTimelineStep
        timeline_step = get_step(timeline, step)

        if timeline_step == nothing
            timeline.table[step] = CollectionTimelineStep.new()
        end

        return timeline.table[step]
    end

    function for_each_gpath(timeline :: ColTimeline, step :: Step, fn_each)
        timeline_step = get_step(timeline, step)

        if timeline_step != nothing
            CollectionTimelineStep.for_each_gpath(timeline_step, fn_each)
        end
    end

    function impact!(timeline :: ColTimeline, step :: Step, gpath :: GPath)
        timeline_step = get_if_dontexiste_create_it!(timeline, step)

        if timeline_step != nothing
            CollectionTimelineStep.impact!(timeline_step, gpath)
        end
    end


end
