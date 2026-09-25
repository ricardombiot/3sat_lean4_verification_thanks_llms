function test_sat_machine_unsat()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    #GraphMap.add_var!(gmap, "y")
    #GraphMap.add_var!(gmap, "w")
    GraphMap.add_gate!(gmap, "x","x","x")
    GraphMap.add_gate!(gmap, "!x","!x","!x")

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == false

    SatMachine.plot_gpaths(machine, "unsat_example")
end


test_sat_machine_unsat()
