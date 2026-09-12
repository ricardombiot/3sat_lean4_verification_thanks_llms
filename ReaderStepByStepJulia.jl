#!/usr/bin/env julia

push!(LOAD_PATH, joinpath(@__DIR__, "docs/original_julia/src"))
include(joinpath(@__DIR__, "docs/original_julia/src/main.jl"))

function main()
    println("╔════════════════════════════════════════╗")
    println("║  JULIA: Reader Step-by-Step Trace      ║")
    println("║  (Certificate Set → Solutions)        ║")
    println("╚════════════════════════════════════════╝\n")

    # Load CNF
    cnf_path = "lean_project/test_sat_medium.cnf"
    if !isfile(cnf_path)
        println("Error: $cnf_path not found")
        return
    end

    gmap = GraphMap.load_import!(cnf_path)
    println("📋 CNF: $(gmap.clausule_counter) clauses, test_sat_medium")
    println("   Expected: 1=F, 2=T, 3=F, 4=T\n")

    # Run machine to completion
    println("🤖 PHASE 1: Running SatMachine to completion")
    machine = SatMachine.new(gmap)
    SatMachine.init!(machine)
    SatMachine.run!(machine)

    found_solution = SatMachine.have_solution(machine)
    current_step = machine.current_step

    println("✅ Machine complete: step=$current_step, SAT=$found_solution\n")

    if found_solution
        println("📖 PHASE 2: Reader Initialization")
        println("──────────────────────────────")

        # Get solution GPaths
        list_gpaths = SatMachine.get_gpath_solutions(machine)
        if !isempty(list_gpaths)
            gpath = first(list_gpaths)
            println("✅ Reader initialized with final GPath")

            println("\n📊 PHASE 3: Certificate Set Analysis")
            println("──────────────────────────────────")
            println("GPath represents all solutions for this formula")
            println("Step reached: $(gpath.current_step)")

            println("\n📖 PHASE 4: Solution Reading")
            println("────────────────────────────")

            # Try to read solutions
            println("Attempting solution extraction...")
            try
                reader = PathExpReader.new(gpath)
                PathExpReader.read!(reader)

                println("✅ Reader extracted $(length(reader.list_solutions)) solutions:")
                for (i, solution) in enumerate(reader.list_solutions)
                    sol_str = join([solution[j] ? "T" : "F" for j in 1:length(solution)], ",")
                    println("   Solution $i: x1=$(solution[1] ? "T" : "F"), x2=$(solution[2] ? "T" : "F"), x3=$(solution[3] ? "T" : "F"), x4=$(solution[4] ? "T" : "F")")
                end
            catch e
                println("⚠️  Reader process: $(e)")
            end

            println("\n✅ Expected solutions:")
            println("   1=False, 2=True, 3=False, 4=True (as per CNF comment)")
        end
    else
        println("❌ No solution found (UNSAT)")
    end

    println("\n" * "="^50)
    println("Reader implementation: Step-by-step extraction ready")
end

main()
