function test_sat_machine_timming(n_clauses)
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    GraphMap.add_var!(gmap, "y")
    GraphMap.add_var!(gmap, "w")

    for i in 1:n_clauses
        GraphMap.add_gate!(gmap, "x","y","w")
    end
    GraphMap.close_gates!(gmap)
    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == true

    SatMachine.plot_gpaths(machine, "example_simple")
end

n_clauses = 10
total_time = @elapsed test_sat_machine_timming(n_clauses)
println("TIME for 3 VARS $n_clauses CLAUSES: $total_time seconds")
