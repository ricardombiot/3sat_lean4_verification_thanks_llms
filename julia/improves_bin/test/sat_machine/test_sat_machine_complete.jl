function test_sat_machine_complete(n)
    gmap = GraphMap.new()

    for i in 1:n
        GraphMap.add_var!(gmap, "$i")
    end

    for i in 1:n
        GraphMap.add_gate!(gmap, "$i","!$i","$i")
    end
    GraphMap.close_gates!(gmap)
    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == true

    SatMachine.plot_gpaths(machine, "gpath_example_complete_$n")
end

n = 1
total_time = @elapsed test_sat_machine_complete(n)
println("TIME for COMPLETE with $n VARS $n CLAUSES: $total_time seconds")
