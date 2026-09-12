#!/usr/bin/env julia

push!(LOAD_PATH, joinpath(@__DIR__, "docs/original_julia/src"))
include(joinpath(@__DIR__, "docs/original_julia/src/main.jl"))

function main()
    println("╔════════════════════════════════════════╗")
    println("║  JULIA: Tseitin Formula Reader Test   ║")
    println("║  (CNF with Tseitin variables)        ║")
    println("╚════════════════════════════════════════╝\n")

    # Load CNF
    cnf_path = "tseitin_test.cnf"
    if !isfile(cnf_path)
        println("Error: $cnf_path not found")
        return
    end

    gmap = GraphMap.load_import!(cnf_path)
    println("📋 CNF: $(gmap.clausule_counter) clauses")
    println("   Variables: $(gmap.var_counter)")
    println("   Tseitin transformation test\n")

    # Run machine to completion
    println("🤖 PHASE 1: Running SatMachine")
    machine = SatMachine.new(gmap)
    SatMachine.init!(machine)
    SatMachine.run!(machine)

    found_solution = SatMachine.have_solution(machine)
    current_step = machine.current_step

    println("✅ Machine complete: step=$current_step, SAT=$found_solution\n")

    if found_solution
        # Get solution GPaths
        list_gpaths = SatMachine.get_gpath_solutions(machine)
        if !isempty(list_gpaths)
            gpath = first(list_gpaths)

            println("📖 PHASE 2: Reading Solutions")
            println("──────────────────────────────")

            try
                reader = PathExpReader.new(gpath)
                PathExpReader.read!(reader)

                solutions = reader.list_solutions
                println("✅ Solutions extracted: $(length(solutions))")
                println("\n📝 All solutions:")

                for (i, solution) in enumerate(solutions)
                    vars_str = join([solution[j] ? "1" : "0" for j in 1:min(6, length(solution))], "")
                    println("   Solution $i: $vars_str")
                end

            catch e
                println("⚠️  Reader process: $(e)")
            end
        end
    else
        println("❌ No solution found (UNSAT)")
    end

    println("\n" * "="^50)
    println("Tseitin test complete")
end

main()
