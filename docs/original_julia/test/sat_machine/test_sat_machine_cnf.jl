function test_sat_machine_cnf_import()
    path_file = "./example_cnf/simple3sat_v3_c2.cnf"
    gmap = GraphMap.load_import!(path_file)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true

    SatMachine.plot_gpaths(machine, "simple3sat_v3_c2_gpath")
end

function test_rand3sat_v8_c10()
    path_file = "./example_cnf/rand3sat_v8_c10.cnf"
    gmap = GraphMap.load_import!(path_file)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true

    #SatMachine.plot_gpaths(machine, "rand3sat_v8_c10")
end


function test_rand3sat_v4_c20()
    path_file = "./example_cnf/rand3sat_v4_c20.cnf"
    gmap = GraphMap.load_import!(path_file)

    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    @test SatMachine.have_solution(machine) == true
end


test_sat_machine_cnf_import()
test_rand3sat_v8_c10()
test_rand3sat_v4_c20()
