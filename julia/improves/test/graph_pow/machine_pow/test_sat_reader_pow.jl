function test_pow_sat_reader()
    path_file = "./example_cnf/simple3sat_v3_c2.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachinePow.new(gmap)
    SatMachinePow.run!(machine)
    @test SatMachinePow.have_solution(machine) == true

    list_gpaths = SatMachinePow.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathPowReader.new(gpath)

    for step in [0,2,4]
        @test reader.step == step

        PathPowReader.read_step!(reader)

        diagram = GraphPowVisual.build(gpath)
        name_file = "reader_step$step"
        GraphPowVisual.to_png(diagram, name_file)
        println("Printing ... $name_file")
    end

    #SatMachinePow.plot_gpaths(machine, "simple3sat_v3_c2_gpath")
end

function test_pow_sat_reader_basic()
    path_file = "./example_cnf/basic_v3_c1.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachinePow.new(gmap)
    SatMachinePow.run!(machine)
    @test SatMachinePow.have_solution(machine) == true

    list_gpaths = SatMachinePow.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathPowReader.new(gpath)
    PathPowReader.read!(reader)

    println("Solution: $(reader.solution)")

    @test CheckerCnf.test(reader.solution, path_file)
end


function test_pow_sat_exp_reader_basic()
    path_file = "./example_cnf/basic_v3_c1.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachinePow.new(gmap)
    SatMachinePow.run!(machine)
    @test SatMachinePow.have_solution(machine) == true

    list_gpaths = SatMachinePow.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathPowExpReader.new(gpath)
    PathPowExpReader.read!(reader)

    println("Solution: $(reader.list_solutions)")

    @test CheckerCnf.test_all(reader.list_solutions, path_file)
end

function test_pow_sat_exp_reader_rand3sat_v4_c20()
    path_file = "./example_cnf/rand3sat_v4_c20.cnf"
    gmap = GraphMap.load_import!(path_file)
    GraphMap.close_gates!(gmap)

    machine = SatMachinePow.new(gmap)
    SatMachinePow.run!(machine)
    @test SatMachinePow.have_solution(machine) == true

    list_gpaths = SatMachinePow.get_gpath_solutions(machine)
    gpath = first(list_gpaths)

    reader = PathPowExpReader.new(gpath)
    PathPowExpReader.read!(reader)

    println("Solution: $(reader.list_solutions)")
    @test CheckerCnf.test_all(reader.list_solutions, path_file)

end

#test_pow_sat_reader()

test_pow_sat_reader_basic()
test_pow_sat_exp_reader_basic()
test_pow_sat_exp_reader_rand3sat_v4_c20()
