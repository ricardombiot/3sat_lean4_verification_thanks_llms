function test_sat_machine_agresive(n)
    gmap = GraphMap.new()

    for i in 1:n
        GraphMap.add_var!(gmap, "$i")
    end
    mult = 10
    for i in 1:n
        for j in 1:mult
            #smoke
            GraphMap.add_gate!(gmap, "$i","!$i","$i")
        end
        if i > 2
            GraphMap.add_gate!(gmap, "$i","!$(i-1)","$(i-2)")
            GraphMap.add_gate!(gmap, "$(i-2)","!$(i-1)","$i")
        end
    end
    GraphMap.close_gates!(gmap)
    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == true

    #SatMachine.plot_gpaths(machine, "gpath_example_complete_$n")
end

n = 7
total_time = @elapsed test_sat_machine_agresive(n)
println("TIME for COMPLETE with $n VARS $(n*10) CLAUSES: $total_time seconds")
