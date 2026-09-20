function test_pow_sat_machine_pow_simple()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    GraphMap.add_var!(gmap, "y")
    GraphMap.add_var!(gmap, "w")
    GraphMap.add_gate!(gmap, "x","y","w")
    GraphMap.close_gates!(gmap)
    machine = SatMachinePow.new(gmap)

    SatMachinePow.init!(machine)
    @test machine.current_step == Step(0)

    for step in 1:8
        SatMachinePow.make_step!(machine)
        @test machine.current_step == step
    end

    @test SatMachinePow.have_solution(machine) == true

    #SatMachinePow.plot_gpaths(machine, "test_pow_sat_machine_pow_simple")
end


function test_pow_sat_machine_unsat()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    #GraphMap.add_var!(gmap, "y")
    #GraphMap.add_var!(gmap, "w")
    GraphMap.add_gate!(gmap, "x","x","x")
    GraphMap.add_gate!(gmap, "!x","!x","!x")

    machine = SatMachinePow.new(gmap)
    SatMachinePow.run!(machine)

    @test SatMachinePow.have_solution(machine) == false

    #SatMachine.plot_gpaths(machine, "unsat_example")
end


test_pow_sat_machine_unsat()
test_pow_sat_machine_pow_simple()
