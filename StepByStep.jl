#!/usr/bin/env julia

# Add the source directory to the path
push!(LOAD_PATH, joinpath(@__DIR__, "docs/original_julia/src"))

include(joinpath(@__DIR__, "docs/original_julia/src/main.jl"))

function debug_step!(machine::SatMachine.MSat, step_num::Int)
    current_step = machine.current_step
    timeline = machine.timeline
    counter = isempty(get_key!(timeline.table, current_step, SatMachine.CollectionTimelineStep.new())) ? 0 :
              timeline.table[current_step].counter_graphs
    finished = SatMachine.is_finished(machine)
    have_paths = SatMachine.have_gpaths_step(machine)

    println("┌─ STEP $step_num ─────────────────────")
    println("│ Current step: $current_step")
    println("│ Counter graphs at step: $counter")
    println("│ Machine finished: $finished")
    println("│ Have paths: $have_paths")
    println("└───────────────────────────────────")
end

function main()
    println("╔════════════════════════════════════════╗")
    println("║  JULIA SatMachine Step-by-Step Trace   ║")
    println("╚════════════════════════════════════════╝\n")

    # Step 1: Create a simple GraphMap
    println("📋 PHASE 1: Creating GraphMap")
    println("─────────────────────────────")

    gmap = GraphMap.new()
    println("GMap created: step=$(gmap.step), clauses=$(gmap.clausule_counter)\n")

    # Step 2: Create SatMachine
    println("🤖 PHASE 2: Initializing SatMachine")
    println("──────────────────────────────────")

    machine = SatMachine.new(gmap)
    println("SatMachine created\n")

    debug_step!(machine, 0)

    # Step 3: Initialize with seed paths
    println("\n🌱 PHASE 3: Initializing seed GPaths")
    println("──────────────────────────────────")

    SatMachine.init!(machine)
    println("Seeds initialized\n")

    debug_step!(machine, 1)

    # Step 4: Execute main loop with tracing
    println("\n▶️  PHASE 4: Executing machine (step by step)")
    println("───────────────────────────────────────────")

    finished_initial = SatMachine.is_finished(machine)
    have_paths_initial = SatMachine.have_gpaths_step(machine)

    if !finished_initial && have_paths_initial
        # Do first step manually
        println("\n➤ Executing make_step! #1")
        SatMachine.make_step!(machine)
        debug_step!(machine, 2)

        # Do second step
        finished2 = SatMachine.is_finished(machine)
        have_paths2 = SatMachine.have_gpaths_step(machine)
        if !finished2 && have_paths2
            println("\n➤ Executing make_step! #2")
            SatMachine.make_step!(machine)
            debug_step!(machine, 3)

            # Do third step
            finished3 = SatMachine.is_finished(machine)
            have_paths3 = SatMachine.have_gpaths_step(machine)
            if !finished3 && have_paths3
                println("\n➤ Executing make_step! #3")
                SatMachine.make_step!(machine)
                debug_step!(machine, 4)

                println("\n⏸️  (trace limited to 3 steps for clarity)")
            else
                println("\n⏹️  Machine stopped after step 2")
            end
        else
            println("\n⏹️  Machine stopped after step 1")
        end
    else
        println("No paths to execute (empty GraphMap)")
    end

    # Step 5: Final results
    println("\n✅ PHASE 5: Final Status")
    println("───────────────────────")

    finished_final = SatMachine.is_finished(machine)
    found_solution = SatMachine.have_solution(machine)

    println("Machine finished: $finished_final")
    println("Solution found: $found_solution")

    if found_solution
        println("\n🎉 SatMachine successfully found a solution!")
    else
        println("\n❌ No solution found (or GraphMap empty)")
    end
end

main()
