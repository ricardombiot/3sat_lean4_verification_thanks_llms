function test_sat_machine_timming_vars(n_vars)
    gmap = GraphMap.new()

    for i in 1:n_vars
        GraphMap.add_var!(gmap, "$i")
    end

    GraphMap.add_gate!(gmap, "1","1","1")
    GraphMap.close_gates!(gmap)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == true

    #SatMachine.plot_gpaths(machine, "example_simple")
end

#n_vars = 5
for n_vars in [5,10,15,20,40,80]
    total_time = @elapsed test_sat_machine_timming_vars(n_vars)
    println("TIME for $n_vars VARS 1 CLAUSES: $total_time seconds")
end
