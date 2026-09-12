#!/usr/bin/env julia

# Add the source directory to the path
push!(LOAD_PATH, joinpath(@__DIR__, "docs/original_julia/src"))

include(joinpath(@__DIR__, "docs/original_julia/src/main.jl"))

function debug_step!(machine::SatMachine.MSat, step_num::Int)
    current_step = machine.current_step
    timeline = machine.timeline

    # Get counter for current step
    counter = 0
    if haskey(timeline.table, current_step)
        counter = timeline.table[current_step].counter_graphs
    end

    finished = SatMachine.is_finished(machine)
    have_paths = SatMachine.have_gpaths_step(machine)

    println("┌─ STEP $step_num ─────────────────────")
    println("│ Current step: $current_step")
    println("│ Counter graphs: $counter")
    println("│ Finished: $finished | Have paths: $have_paths")
    println("└───────────────────────────────────")
end

function main()
    println("╔════════════════════════════════════════╗")
    println("║  JULIA: Simple CNF Step-by-Step Trace  ║")
    println("╚════════════════════════════════════════╝\n")

    # Step 1: Load CNF
    println("📋 PHASE 1: Loading CNF")
    println("─────────────────────────────")

    cnf_path = "lean_project/convergence_test.cnf"
    if !isfile(cnf_path)
        println("Error: $cnf_path not found.")
        return
    end

    gmap = GraphMap.load_import!(cnf_path)
    println("✅ CNF Loaded: step=$(gmap.step), clauses=$(gmap.clausule_counter)\n")

    # Step 2: Create SatMachine
    println("🤖 PHASE 2: Initializing SatMachine")
    println("──────────────────────────────────")

    machine = SatMachine.new(gmap)
    println("✅ SatMachine created\n")

    debug_step!(machine, 0)

    # Step 3: Initialize with seed paths
    println("\n🌱 PHASE 3: Initializing seed GPaths")
    println("──────────────────────────────────")

    SatMachine.init!(machine)
    println("✅ Seeds initialized\n")

    debug_step!(machine, 1)

    # Step 4: Execute main loop with tracing
    println("\n▶️  PHASE 4: Executing machine (step by step)")
    println("───────────────────────────────────────────")

    finished_initial = SatMachine.is_finished(machine)
    have_paths_initial = SatMachine.have_gpaths_step(machine)

    if !finished_initial && have_paths_initial
        # Iteration 1
        println("\n➤ Iteration 1")
        SatMachine.make_step!(machine)
        debug_step!(machine, 2)

        finished2 = SatMachine.is_finished(machine)
        have_paths2 = SatMachine.have_gpaths_step(machine)
        if !finished2 && have_paths2
            # Iteration 2
            println("\n➤ Iteration 2")
            SatMachine.make_step!(machine)
            debug_step!(machine, 3)

            finished3 = SatMachine.is_finished(machine)
            have_paths3 = SatMachine.have_gpaths_step(machine)
            if !finished3 && have_paths3
                # Iteration 3
                println("\n➤ Iteration 3")
                SatMachine.make_step!(machine)
                debug_step!(machine, 4)

                finished4 = SatMachine.is_finished(machine)
                have_paths4 = SatMachine.have_gpaths_step(machine)
                if !finished4 && have_paths4
                    # Iteration 4
                    println("\n➤ Iteration 4")
                    SatMachine.make_step!(machine)
                    debug_step!(machine, 5)

                    finished5 = SatMachine.is_finished(machine)
                    have_paths5 = SatMachine.have_gpaths_step(machine)
                    if !finished5 && have_paths5
                        # Iteration 5
                        println("\n➤ Iteration 5")
                        SatMachine.make_step!(machine)
                        debug_step!(machine, 6)
                        println("\n⏸️  (Trace showing first 5 iterations)")
                    else
                        println("\n⏹️  Machine completed")
                    end
                else
                    println("\n⏹️  Machine completed")
                end
            else
                println("\n⏹️  Machine completed")
            end
        else
            println("\n⏹️  Machine completed")
        end
    else
        println("No paths to execute")
    end

    # Step 5: Final results
    println("\n✅ PHASE 5: Final Status")
    println("───────────────────────")

    finished_final = SatMachine.is_finished(machine)
    found_solution = SatMachine.have_solution(machine)

    println("Machine finished: $finished_final")
    println("Solution found: $found_solution")

    if found_solution
        println("\n🎉 SatMachine successfully found a solution! ✅")
    else
        println("\n❌ No solution found")
    end
end

main()
