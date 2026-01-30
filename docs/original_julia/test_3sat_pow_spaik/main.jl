include("./../src/main.jl")

function main()
    base_path_instances = "./output/instances"
    base_path_solver_ex = "./output/solver_exhaustive"
    base_path_solver_machine = "./output/solver_sat_machine"
    base_path_solver_machine_pow = "./output/solver_sat_machine_pow"

    list_instances = readdir(base_path_instances)

    total_time = 0
    total_instances = length(list_instances)
    counter = 0
    for instance_file in list_instances
        if contains(instance_file, ".cnf")
            counter += 1
            path_instance = "$base_path_instances/$instance_file"
            solver_instance_file = replace("$instance_file", ".cnf" => ".txt")
            path_output_solver_ex = "$base_path_solver_ex/$solver_instance_file"
            path_output_solver_machine = "$base_path_solver_machine/$solver_instance_file"
            path_output_solver_machine_pow = "$base_path_solver_machine_pow/$solver_instance_file"

            #only execution time...
            total_time_ex = solver_ex(path_instance, path_output_solver_ex)
            #println("... $total_time_ex segs")
            total_time_ex = trunc(total_time_ex, digits=2)
            total_time_machine = solver_machine(path_instance, path_output_solver_machine)
            total_time_machine = trunc(total_time_machine, digits=2)

            total_time_machine_pow = solver_machine_pow(path_instance, path_output_solver_machine_pow)
            total_time_machine_pow = trunc(total_time_machine_pow, digits=2)


            if total_time_machine_pow < total_time_machine
                spaik_improvement = trunc( (1 - (total_time_machine_pow/total_time_machine)) * 100, digits=2)
            else
                spaik_improvement = trunc( (1 - (total_time_machine/total_time_machine_pow)) * -100 , digits=2)
            end

            total_time_instance = trunc(total_time_ex+total_time_machine+total_time_machine_pow, digits=3)
            total_time += trunc(total_time_instance, digits=3)
            rest_instances = total_instances-counter
            if rest_instances == 0
                estimation_time_min = 0
            else
                avg_time = total_time/counter
                estimation_time_min = trunc( (rest_instances * avg_time) / 60, digits=2)
            end
            total_time_min = trunc(total_time / 60, digits=2)

            println("- - - - - - - - - - - - - -")
            println("Instance: $counter/$total_instances ")
            println("  Exponential:$total_time_ex segs")
            println("  Machine: $total_time_machine segs")
            println("  MachinePow: $total_time_machine_pow seg  [$spaik_improvement%]")
            println("  ## Total: $total_time_instance seg")
            println("[Total Time: $total_time_min min]")
            println("[Estimation to finishied: $estimation_time_min min]")
            println("- - - - - - - - - - - - - -")

        end
    end

end


function solver_ex(path_instance, path_output_solver_ex)
    println("ExhaustiveSolver: [WORKING ON $path_instance]")
    solver = ExhaustiveSolver.new(path_instance)
    execution_time = @elapsed ExhaustiveSolver.run!(solver)

    open(path_output_solver_ex, "w") do io
        if isempty(solver.list_solutions)
            write(io, "UNSAT\n")
        else
            write(io, "SAT\n")
            for solution in solver.list_solutions
                txt_solution = solution_to_string(solution)
                write(io, "$txt_solution\n")
            end
        end
    end;

    return execution_time
end

function solver_machine(path_instance, path_output_solver_machine)
    println("SolverSatMachine: [WORKING ON $path_instance]")
    gmap = GraphMap.load_import!(path_instance)
    machine = SatMachine.new(gmap)
    execution_time = @elapsed SatMachine.run!(machine)

    is_sat = false
    list_solutions = []
    if SatMachine.have_solution(machine)
        is_sat = true
        list_gpaths = SatMachine.get_gpath_solutions(machine)
        gpath = first(list_gpaths)

        reader = PathExpReader.new(gpath)
        PathExpReader.read!(reader)
        list_solutions = reader.list_solutions
    end

    #println("Solution: $(reader.list_solutions)")
    #@test CheckerCnf.test_all(reader.list_solutions, path_file)

    open(path_output_solver_machine, "w") do io
        if is_sat
            write(io, "SAT\n")
            for solution in list_solutions
                txt_solution = solution_to_string(solution)
                write(io, "$txt_solution\n")
            end
        else
            write(io, "UNSAT\n")
        end
    end;

    return execution_time
end

function solver_machine_pow(path_instance, path_output_solver_machine_pow)
    println("SolverSatMachinePow (Spaik): [WORKING ON $path_instance]")
    gmap = GraphMap.load_import!(path_instance)
    machine = SatMachinePow.new(gmap)
    execution_time = @elapsed SatMachinePow.run!(machine)
    is_sat = false
    list_solutions = []
    if SatMachinePow.have_solution(machine)
        is_sat = true
        list_gpaths = SatMachinePow.get_gpath_solutions(machine)
        gpath = first(list_gpaths)

        reader = PathPowExpReader.new(gpath)
        PathPowExpReader.read!(reader)
        list_solutions = reader.list_solutions
    end

    #println("Solution: $(reader.list_solutions)")
    #@test CheckerCnf.test_all(reader.list_solutions, path_file)

    open(path_output_solver_machine_pow, "w") do io
        if is_sat
            write(io, "SAT\n")
            for solution in list_solutions
                txt_solution = solution_to_string(solution)
                write(io, "$txt_solution\n")
            end
        else
            write(io, "UNSAT\n")
        end
    end;

    return execution_time
end

function solution_to_string(solution :: BitArray{1}) :: String
    txt_solution = ""
    for bit in solution
        if bit
            txt_solution *= "1"
        else
            txt_solution *= "0"
        end
    end

    return txt_solution
end

main()
