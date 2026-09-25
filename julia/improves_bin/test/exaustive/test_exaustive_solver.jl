function test_ex_solver_basic()
    path_file = "./example_cnf/basic_v3_c1.cnf"
    solver = ExhaustiveSolver.new(path_file)

    @test solver.n_literals == 3
    @test solver.last_case == (2^3)-1
    @test solver.gates_or == [[1,2,3]]


    ExhaustiveSolver.run!(solver)
    @test Set(solver.list_solutions) == Set([[1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]])
end

function test_ex_solver()
    path_file = "./example_cnf/rand3sat_v4_c20.cnf"
    solver = ExhaustiveSolver.new(path_file)

    @test solver.n_literals == 4
    @test solver.last_case == (2^4)-1

    ExhaustiveSolver.run!(solver)
    println(solver.list_solutions)
end

test_ex_solver_basic()
test_ex_solver()
