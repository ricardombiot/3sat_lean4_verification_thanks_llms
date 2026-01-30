module SatMachinePow

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias

    using Main.AbsSat.DBMachine.CollectionTimelinePowStep: ColTimelinePowStep
    using Main.AbsSat.DBMachine.CollectionTimelinePowStep

    using Main.AbsSat.DBMachine.CollectionTimelinePow: ColTimelinePow
    using Main.AbsSat.DBMachine.CollectionTimelinePow

    using Main.AbsSat.GraphMap: GMap
    using Main.AbsSat.GraphMap
    using Main.AbsSat.GraphPow: GPow
    using Main.AbsSat.GraphPow

    using Main.AbsSat.GraphPowVisual

    mutable struct MSatPow
        gmap :: GMap
        timeline :: ColTimelinePow
        current_step :: Step
    end

    function new(gmap :: GMap)
        #=if gmap.stage != "end"
            println("Close GMap..")
            gmap = deepcopy(gmap)
            GraphMap.close_gates!(gmap)
        end
        =#

        timeline = CollectionTimelinePow.new()
        current_step = Step(0)
        MSatPow(gmap, timeline, current_step)
    end

    function init!(machine :: MSatPow)
        GraphMap.for_each_node_step(machine.gmap, Step(0), function (map_node)
            id = map_node.id
            title = map_node.title
            CollectionTimelinePow.init_gpath_seed!(machine.timeline, id, title)
        end)
    end

    function run!(machine :: MSatPow)
        init!(machine)
        #=while is_valid_execution!(machine)
            println("Step: $(machine.current_step)/$(machine.gmap.step)")

        end
        =#
        execute_step!(machine)
    end

    function execute_step!(machine :: MSatPow)
        #println("Step: $(machine.current_step)/$(machine.gmap.step)")
        if !is_finished(machine) && have_gpaths_step(machine)
            make_step!(machine)
            execute_step!(machine)
        #else
        #    println("Machine Halt...")
        end
    end

    function is_finished(machine :: MSatPow)
        machine.gmap.step-1 == machine.current_step
    end

    function have_solution(machine :: MSatPow)
        return is_finished(machine) && have_gpaths_step(machine)
    end

    #=
    function is_valid_execution!(machine :: MSatPow)
        is_finished = machine.gmap.step+1 == machine.current_step
        return !is_finished && have_gpaths_step(machine)
    end
    =#

    function make_step!(machine :: MSatPow)
        current_step = machine.current_step
        CollectionTimelinePow.for_each_gpath(machine.timeline, current_step, function (gpath)
            for_each_destine!(machine, gpath)
        end)

        #println("Remove_line: $current_step ")
        CollectionTimelinePow.remove_line!(machine.timeline, current_step)
        machine.current_step += 1

        #n_graphs = CollectionTimelinePow.get_counter_graphs_step(machine.timeline, machine.current_step)
        #println("Next step, $(machine.current_step) have: $n_graphs gpaths")
    end

    function for_each_destine!(machine :: MSatPow, inmutable_gpath :: GPow)
        map_id_node = inmutable_gpath.map_parent_id
        #println("For each destine...")
        map_node = GraphMap.get_node(machine.gmap, map_id_node)

        for id_destine in map_node.sons
            #println("For each destine... $id_destine")
            send_to_destine!(machine, inmutable_gpath, id_destine)
        end
    end

    function send_to_destine!(machine :: MSatPow, inmutable_gpath :: GPow, id_destine :: NodeId)
        map_node_destine = GraphMap.get_node(machine.gmap, id_destine)
        title_selected_node = map_node_destine.title
        requires = map_node_destine.requires

        gpath = deepcopy(inmutable_gpath)
        GraphPow.do_up_filtering!(gpath, requires, id_destine)
        register_kind_step!(machine, gpath, title_selected_node)

        if gpath.is_valid
            next_step = machine.current_step + 1
            #println("gpath to $next_step")
            CollectionTimelinePow.impact!(machine.timeline, next_step, gpath)
        #else
        #    println("gpath rejected... after up... $title")
        end
    end

    function register_kind_step!(machine :: MSatPow, gpath :: GPow, title_selected_node :: String)
        is_or = contains(title_selected_node, "or")
        is_fusion = contains(title_selected_node, "FusionNode")

        if is_or
            GraphPow.register_step_of_fusion_ors!(gpath, machine.current_step)
        elseif is_fusion
            GraphPow.register_step_of_fusion_nodes!(gpath, machine.current_step)
        end
    end

    function have_gpaths_step(machine :: MSatPow) :: Bool
        return CollectionTimelinePow.get_counter_graphs_step(machine.timeline, machine.current_step) > 0
    end

    function get_gpath_solutions(machine :: MSatPow) :: Array{GPow,1}
        list_gpaths = Array{GPow,1}()
        CollectionTimelinePow.for_each_gpath(machine.timeline, machine.current_step, function (gpath)
            push!(list_gpaths, gpath)
        end)

        return list_gpaths
    end

    function plot_gpaths(machine :: MSatPow, name :: String)
        CollectionTimelinePow.for_each_gpath(machine.timeline, machine.current_step, function (gpath)
            map_id = gpath.map_parent_id
            id_txt = Alias.as_key(map_id)

            #println("####### Clear before plot....")
            #GraphPow.clean_invalid_nodes!(gpath)
            #println("####### End clear before plot....")

            diagram = GraphPowVisual.build(gpath)
            name_file = "$(name)_gpath_$id_txt"
            GraphPowVisual.to_png(diagram, name_file)
            println("Printing ... $name_file")
        end)
    end

end
