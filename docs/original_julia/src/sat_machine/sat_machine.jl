module SatMachine

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias

    using Main.AbsSat.DBMachine.CollectionTimelineStep: ColTimelineStep
    using Main.AbsSat.DBMachine.CollectionTimelineStep

    using Main.AbsSat.DBMachine.CollectionTimeline: ColTimeline
    using Main.AbsSat.DBMachine.CollectionTimeline

    using Main.AbsSat.GraphMap: GMap
    using Main.AbsSat.GraphMap
    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    using Main.AbsSat.GraphPathVisual

    mutable struct MSat
        gmap :: GMap
        timeline :: ColTimeline
        current_step :: Step
    end

    function new(gmap :: GMap)
        timeline = CollectionTimeline.new()
        current_step = Step(0)
        MSat(gmap, timeline, current_step)
    end

    function init!(machine :: MSat)
        #! [fn-iter] $ O(2) $
        GraphMap.for_each_node_step(machine.gmap, Step(0), function (map_node)
            id = map_node.id
            title = map_node.title
            CollectionTimeline.init_gpath_seed!(machine.timeline, id, title)
        end)
    end

    function run!(machine :: MSat)
        init!(machine)
        execute_step!(machine)
    end

    function execute_step!(machine :: MSat)
        #println("Step: $(machine.current_step)/$(machine.gmap.step)")

        #! [recursive-if] $ O(S) $
        if !is_finished(machine) && have_gpaths_step(machine)
            make_step!(machine)
            execute_step!(machine)
        #else
        #    println("Machine Halt...")
        end
    end

    function is_finished(machine :: MSat)
        machine.gmap.step-1 == machine.current_step
    end

    function have_solution(machine :: MSat)
        return is_finished(machine) && have_gpaths_step(machine)
    end

    function make_step!(machine :: MSat)
        current_step = machine.current_step

        #! [fn-iter] $ O(7) $
        CollectionTimeline.for_each_gpath(machine.timeline, current_step, function (gpath)
            send_to_destine_by_origin!(machine, gpath)
        end)

        #println("Remove_line: $current_step ")
        CollectionTimeline.remove_line!(machine.timeline, current_step)
        machine.current_step += 1

        #n_graphs = CollectionTimeline.get_counter_graphs_step(machine.timeline, machine.current_step)
        #println("Next step, $(machine.current_step) have: $n_graphs gpaths")
    end

    function send_to_destine_by_origin!(machine :: MSat, inmutable_gpath :: GPath)
        map_id_node = inmutable_gpath.map_parent_id
        #println("For each destine...")
        map_node = GraphMap.get_node(machine.gmap, map_id_node)

        #! [for] $ O(7) $
        for id_destine in map_node.sons
            #println("For each destine... $id_destine")
            send_to_destine!(machine, inmutable_gpath, id_destine)
        end
    end

    function send_to_destine!(machine :: MSat, inmutable_gpath :: GPath, id_destine :: NodeId)
        map_node_destine = GraphMap.get_node(machine.gmap, id_destine)
        title = map_node_destine.title
        requires = map_node_destine.requires

        gpath = deepcopy(inmutable_gpath)
        GraphPath.do_up_filtering!(gpath, requires, id_destine, title)

        if gpath.is_valid
            next_step = machine.current_step + 1
            #println("gpath to $next_step")
            CollectionTimeline.impact!(machine.timeline, next_step, gpath)
        #else
        #    println("gpath rejected... after up... $title")
        end
    end

    function have_gpaths_step(machine :: MSat) :: Bool
        return CollectionTimeline.get_counter_graphs_step(machine.timeline, machine.current_step) > 0
    end

    function get_gpath_solutions(machine :: MSat) :: Array{GPath,1}
        if have_solution(machine)
            return get_gpath_list(machine)
        else
            return []
        end
    end

    function get_gpath_list(machine :: MSat) :: Array{GPath,1}
        list_gpaths = Array{GPath,1}()
        #! [fn-iter] $ O(7) $
        CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, function (gpath)
            Base.push!(list_gpaths, gpath)
        end)

        return list_gpaths
    end

    function plot_gpaths(machine :: MSat, name :: String)
        #! [fn-iter] $ O(7*7) $
        CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, function (gpath)
            map_id = gpath.map_parent_id
            id_txt = Alias.as_key(map_id)

            #println("####### Clear before plot....")
            #GraphPath.clean_invalid_nodes!(gpath)
            #println("####### End clear before plot....")

            diagram = GraphPathVisual.build(gpath)
            name_file = "$(name)_gpath_$id_txt"
            GraphPathVisual.to_png(diagram, name_file)
            println("Printing ... $name_file")
        end)
    end

end
