include("./../src/main.jl")

function main()
    base_path_instances = "./output/instances"
    base_path_solver_ex = "./output/solver_exhaustive"
    base_path_solver_machine = "./output/solver_sat_machine"

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


            total_time_ex = @elapsed solver_ex(path_instance, path_output_solver_ex)
            #println("... $total_time_ex segs")
            total_time_ex = trunc(total_time_ex, digits=2)
            total_time_machine = @elapsed solver_machine(path_instance, path_output_solver_machine)
            #println("... $total_time_machine segs")
            total_time_machine = trunc(total_time_machine, digits=2)
            total_time_instance = total_time_ex+total_time_machine
            total_time += trunc(total_time_instance, digits=3)
            rest_instances = total_instances-counter
            if rest_instances == 0
                estimation_time_min = 0
            else
                estimation_time_min = trunc( (rest_instances * total_time_instance) / 60, digits=2)
            end
            total_time_min = trunc(total_time / 60, digits=2)

            println("Instance: $counter/$total_instances Time Ex: $total_time_ex segs Machine: $total_time_machine segs Total: $total_time_instance")
            println("Time: $total_time_min min | Estimation to finishied: $estimation_time_min min")
        end
    end

end


function solver_ex(path_instance, path_output_solver_ex)
    println("ExhaustiveSolver: [WORKING ON $path_instance]")
    solver = ExhaustiveSolver.new(path_instance)
    ExhaustiveSolver.run!(solver)

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

end

function solver_machine(path_instance, path_output_solver_machine)
    println("SolverSatMachine: [WORKING ON $path_instance]")
    gmap = GraphMap.load_import!(path_instance)
    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
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
