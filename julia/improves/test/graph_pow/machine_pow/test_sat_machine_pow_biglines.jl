function test_sat_machine_timming_pow_biglines(n_clauses)
    gmap = GraphMap.new()

    n_vars = n_clauses*3

    for i in 1:n_vars
        GraphMap.add_var!(gmap, "$i")
    end

    for i in 1:n_clauses
        l1 = 1+(i-1)*3
        l2 = l1 + 1
        l3 = l1 + 2

        #println("GATE: $l1 $l2 $l3")
        GraphMap.add_gate!(gmap, "$l1","$l2","$l3")
    end
    GraphMap.close_gates!(gmap)
    machine = SatMachinePow.new(gmap)
    SatMachinePow.run!(machine)

    @test SatMachinePow.have_solution(machine) == true

    #SatMachinePow.plot_gpaths(machine, "biglines_$(n_clauses-1)_")
    list_gpaths = SatMachinePow.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    #=
    max_num_nodes = get_max_number_of_nodes(gpath)

    if n_clauses >= 2
        # 7 nodes * 7 Ups
        @test max_num_nodes == 7*7


        total_nodes = get_total_nodes(gpath)
        expected_total_nodes_by_literals = n_vars*4+(n_vars-1)*2
        expected_total_nodes_by_clauses = 7+((n_clauses-1)*7^2)
        expected_total_nodes_fusion = 2+7
        expected_total = expected_total_nodes_by_literals + expected_total_nodes_by_clauses + expected_total_nodes_fusion
        @test total_nodes == expected_total
    end
    =#

end

#=
function get_max_number_of_nodes(gpath) :: Int64
    max_nodes = 0
    for (step, col_nodes) in gpath.table_lines.table
        max_nodes = max(max_nodes,col_nodes.count)
    end
    return max_nodes
end

function get_total_nodes(gpath) :: Int64
    total_nodes = 0
    for (step, col_nodes) in gpath.table_lines.table
        total_nodes += col_nodes.count
    end
    return total_nodes
end
=#

for i in 2:8
    n_clauses = i
    n_vars = n_clauses*3
    total_time = @elapsed test_sat_machine_timming_pow_biglines(n_clauses)
    println("TIME for $n_vars VARS $n_clauses CLAUSES: $total_time seconds")
end
