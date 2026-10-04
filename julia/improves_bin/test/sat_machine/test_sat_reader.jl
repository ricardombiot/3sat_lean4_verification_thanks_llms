function test_sat_reader()
    path_file = "./example_cnf/simple3sat_v3_c2.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true

    list_gpaths = SatMachine.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathReader.new(gpath)

    for step in [0,2,4]
        @test reader.step == step

        PathReader.read_step!(reader)

        diagram = GraphPathVisual.build(gpath)
        name_file = "reader_step$step"
        GraphPathVisual.to_png(diagram, name_file)
        println("Printing ... $name_file")
    end

    #SatMachine.plot_gpaths(machine, "simple3sat_v3_c2_gpath")
end

function test_sat_reader_basic()
    path_file = "./example_cnf/basic_v3_c1.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true

    list_gpaths = SatMachine.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathReader.new(gpath)
    PathReader.read!(reader)

    println("Solution: $(reader.solution)")

    @test CheckerCnf.test(reader.solution, path_file)
end


function test_sat_exp_reader_basic()
    path_file = "./example_cnf/basic_v3_c1.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true

    list_gpaths = SatMachine.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathExpReader.new(gpath)
    PathExpReader.read!(reader)

    println("Solution: $(reader.list_solutions)")

    @test CheckerCnf.test_all(reader.list_solutions, path_file)
end

function test_sat_exp_reader_rand3sat_v4_c20()
    path_file = "./example_cnf/rand3sat_v4_c20.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true

    list_gpaths = SatMachine.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathExpReader.new(gpath)
    PathExpReader.read!(reader)

    println("Solution: $(reader.list_solutions)")
    @test CheckerCnf.test_all(reader.list_solutions, path_file)

end

test_sat_reader()

test_sat_reader_basic()
test_sat_exp_reader_basic()
test_sat_exp_reader_rand3sat_v4_c20()
