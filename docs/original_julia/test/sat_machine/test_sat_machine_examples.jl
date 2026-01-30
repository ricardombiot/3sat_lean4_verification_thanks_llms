function test_example_simple()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "1")
    GraphMap.add_var!(gmap, "2")
    GraphMap.add_var!(gmap, "3")

    GraphMap.add_gate!(gmap, "1","2","3")
    GraphMap.close_gates!(gmap)

    diagram = GraphMapVisual.build(gmap)
    GraphMapVisual.to_png(diagram, "example_simple_map")

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == true
    SatMachine.plot_gpaths(machine, "example_simple_gpath")
end


function test_example_simple49()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "1")
    GraphMap.add_var!(gmap, "2")
    GraphMap.add_var!(gmap, "3")

    GraphMap.add_var!(gmap, "4")
    GraphMap.add_var!(gmap, "5")
    GraphMap.add_var!(gmap, "6")

    GraphMap.add_var!(gmap, "7")
    GraphMap.add_var!(gmap, "8")
    GraphMap.add_var!(gmap, "9")

    GraphMap.add_gate!(gmap, "1","2","3")
    GraphMap.add_gate!(gmap, "4","5","6")
    GraphMap.add_gate!(gmap, "7","8","9")
    GraphMap.close_gates!(gmap)

    diagram = GraphMapVisual.build(gmap)
    GraphMapVisual.to_png(diagram, "example_simple_map49")

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == true
    SatMachine.plot_gpaths(machine, "example_simple_gpath49")
end

#test_example_simple()
test_example_simple49()
