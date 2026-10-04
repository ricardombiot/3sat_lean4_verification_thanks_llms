function test_build_map_vars(n_vars)
    gmap = GraphMap.new()

    for var in 0:n_vars
        GraphMap.add_var!(gmap, "v$var")
    end
end

function test_build_map_full_nn(n)
    gmap = GraphMap.new()
    n_vars = n
    n_gates = n
    for var in 0:n_vars
        GraphMap.add_var!(gmap, "v$var")
    end

    for gate in 0:n_gates
        GraphMap.add_gate!(gmap, "v0", "v0", "v0")
    end
end

println("Timming building maps Nvars without caulsules....")
for n_vars in [10,25,50,100,250,500,1000]
    total_time = @elapsed test_build_map_vars(n_vars)
    println("TIME BUILDING MAP $n_vars VARS: $total_time seconds")
end


println("Timming building maps Nvars*Nclauses....")
for n in [10,25,50,100,250,500,1000]
    total_time = @elapsed test_build_map_full_nn(n)
    println("TIME BUILDING MAP $n VARS $n CLAUSES: $total_time seconds")
end
