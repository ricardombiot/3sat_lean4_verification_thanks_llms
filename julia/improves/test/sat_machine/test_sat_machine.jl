function test_sat_machine()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    GraphMap.add_var!(gmap, "y")
    GraphMap.add_var!(gmap, "w")
    GraphMap.add_gate!(gmap, "x","y","w")

    machine = SatMachine.new(gmap)

    SatMachine.init!(machine)
    @test machine.current_step == Step(0)

    for step in 1:7
        SatMachine.make_step!(machine)
        @test machine.current_step == step
    end
    #SatMachine.make_step!(machine)
    #@test machine.current_step == Step(2)


    CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, function (gpath)
        map_id = gpath.map_parent_id
        id_txt = Alias.as_key(map_id)

        diagram = GraphPathVisual.build(gpath)
        name_file = "gpath_$id_txt"
        GraphPathVisual.to_png(diagram, name_file)
        println("Printing ... $name_file")
    end)
end


test_sat_machine()
