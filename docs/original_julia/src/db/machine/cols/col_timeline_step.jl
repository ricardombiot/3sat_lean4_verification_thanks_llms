module CollectionTimelineStep
    using Main.AbsSat.Alias: Step, NodeId

    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    mutable struct ColTimelineStep
        table :: Dict{NodeId, GPath}
        counter_graphs :: Int8
    end

    function new()
        table = Dict{NodeId, GPath}()
        counter_graphs = 0
        ColTimelineStep(table, counter_graphs)
    end

    function for_each_gpath(timeline_step :: ColTimelineStep, fn_each)
        for (node_id, gpath) in timeline_step.table
            fn_each(gpath)
        end
    end

    function get_gpath!(timeline_step :: ColTimelineStep, map_node_id :: NodeId) :: Union{GPath,Nothing}
        if haskey(timeline_step.table, map_node_id)
            return timeline_step.table[map_node_id]
        else
            return nothing
        end
    end

    function impact!(timeline_step :: ColTimelineStep, gpath :: GPath)
        if gpath.is_valid
            map_node_id = gpath.map_parent_id
            current_gpath = get_gpath!(timeline_step, map_node_id)
            if current_gpath == nothing
                timeline_step.table[map_node_id] = gpath
                timeline_step.counter_graphs += 1
            else
                GraphPath.do_join!(current_gpath, gpath)
            end
        end
    end



end
