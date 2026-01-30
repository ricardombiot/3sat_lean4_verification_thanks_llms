using Test
include("./../src/main.jl")

#=
@time @testset "AbsSat" begin
    include("test_hello.jl")
end
=#

@time @testset "GraphMap" begin
    include("./db/map/docs/test_node.jl")
    include("./db/map/cols/test_nodes.jl")
    include("./db/map/cols/test_lines.jl")
    include("./db/map/cols/test_vars.jl")

    include("./graph_map/test_graph_map_vars.jl")
    include("./graph_map/test_graph_map_gates.jl")
    include("./graph_map/test_graph_map_import.jl")
end




@time @testset "Machine" begin

    include("./db/machine/cols/test_timeline.jl")
    #include("./sat_machine/test_sat_machine.jl")
    #include("./sat_machine/test_sat_machine_unsat.jl")
    #include("./sat_machine/test_sat_machine_building_map.jl")

    #include("./sat_machine/test_sat_machine_timming.jl")
    #include("./sat_machine/test_sat_machine_timming_vars.jl")
    #include("./sat_machine/test_sat_machine_complete.jl")
    include("./sat_machine/test_sat_machine_examples.jl")
    #include("./sat_machine/test_sat_machine_cnf.jl")

    #include("./sat_machine/test_sat_reader.jl")
    #include("./sat_machine/test_sat_machine_biglines.jl")
end


@time @testset "ExaustiveSolver" begin
    include("./exaustive/test_exaustive_solver.jl")
end


@time @testset "GraphPath" begin
    include("./db/path/docs/test_simulation_nodes.jl")
    include("./db/path/cols/test_nodes.jl")
    include("./db/path/cols/test_lines.jl")

    include("./graph_path/test_graph_path.jl")
    include("./graph_path/test_graph_path_join.jl")
end
#==#

#=
@time @testset "GraphPow" begin
    include("./graph_pow/test_graph_pow.jl")
    include("./graph_pow/test_graph_pow_join.jl")
end
=#

#=
@time @testset "SatMachinePow" begin
    include("./graph_pow/machine_pow/test_sat_machine_pow.jl")
    #include("./graph_pow/machine_pow/test_sat_machine_pow_biglines.jl")
    include("./graph_pow/machine_pow/test_sat_machine_pow_cnf.jl")
    include("./graph_pow/machine_pow/test_sat_reader_pow.jl")
end
=#
