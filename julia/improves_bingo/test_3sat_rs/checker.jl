function main()
    base_path_instances = "./output/instances"
    base_path_solver_ex = "./output/solver_exhaustive"
    base_path_solver_machine = "./output/solver_sat_machine"
    base_path_solver_machine_pow = "./output/solver_sat_machine_pow"
    path_report = "./output/report.txt"
    list_instances = readdir(base_path_instances)

    n_instances = 0
    n_valid_machine_sat = 0
    n_valid_machine_pow_sat = 0
    n_unsat = 0
    for instance_file in list_instances
        if contains(instance_file, ".cnf")

            path_instance = "$base_path_instances/$instance_file"
            solver_instance_file = replace("$instance_file", ".cnf" => ".txt")
            path_output_solver_ex = "$base_path_solver_ex/$solver_instance_file"
            path_output_solver_machine = "$base_path_solver_machine/$solver_instance_file"
            path_output_solver_machine_pow = "$base_path_solver_machine_pow/$solver_instance_file"


            solver_ex_file_content = Set(readlines(path_output_solver_ex))
            solver_machine_file_content = Set(readlines(path_output_solver_machine))
            solver_machine_pow_file_content = Set(readlines(path_output_solver_machine_pow))

            if solver_ex_file_content == solver_machine_file_content
                n_valid_machine_sat += 1
            end

            if solver_ex_file_content == solver_machine_pow_file_content
                n_valid_machine_pow_sat += 1
            end

            if solver_ex_file_content == Set(["UNSAT"])
                n_unsat += 1
            end


            n_instances+= 1
        end
    end

    ratio_machine_sat = (n_valid_machine_sat/n_instances)*100
    ratio_machine_pow_sat = (n_valid_machine_pow_sat/n_instances)*100

    report_lines = ["Num. Instance: $n_instances",
            "Num. Valid Machine Sat: $n_valid_machine_sat",
            "Num. Valid Machine Sat: $n_valid_machine_pow_sat",
            "Ratio MSat: $ratio_machine_sat",
            "Ratio MSatPow: $ratio_machine_pow_sat",
            "- - -", "Num. UNSAT instances: $n_unsat"]
    write_report!(path_report, report_lines)


end

function write_report!(path_report, lines)
    println("WRITING REPORT:")
    open(path_report, "w") do io
        for line in lines
            println(line)
            write(io, "$line\n")
        end
    end
end

main()
