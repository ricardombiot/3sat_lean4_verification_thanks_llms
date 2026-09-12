#!/usr/bin/env julia

# Add the source directory to the path
push!(LOAD_PATH, joinpath(@__DIR__, "docs/original_julia/src"))

include(joinpath(@__DIR__, "docs/original_julia/src/main.jl"))

function build_diagram_dot(gpath::GraphPath.GPath)::String
    txt = "digraph G {\n"
    txt *= "  compound=true\n"
    txt *= "  rankdir=LR\n"

    # Draw each step
    for step in 0:(gpath.current_step-1)
        txt *= draw_step_dot(gpath, step)
    end

    # Draw edges
    for step in 0:(gpath.current_step-1)
        txt *= draw_edges_dot(gpath, step)
    end

    txt *= "}\n"
    return txt
end

function draw_step_dot(gpath::GraphPath.GPath, step::Int)::String
    txt = "  subgraph cluster_step_$step {\n"
    txt *= "    style=filled\n"
    txt *= "    color=lightgrey\n"
    txt *= "    node [style=filled,color=white]\n"

    table_lines = gpath.table_lines
    if haskey(table_lines.table, step)
        line = table_lines.table[step]
        for (node_id, node) in line.table
            key_str = replace(Alias.as_key(node_id), "." => "_")
            txt *= "    $key_str [label=\"$(node.title)\"]\n"
        end
    end

    txt *= "    fontsize=12\n"
    txt *= "    label=\"Step $step\"\n"
    txt *= "  }\n"
    return txt
end

function draw_edges_dot(gpath::GraphPath.GPath, step::Int)::String
    txt = ""
    table_lines = gpath.table_lines

    if haskey(table_lines.table, step)
        line = table_lines.table[step]
        for (node_id, node) in line.table
            key_origin = replace(Alias.as_key(node_id), "." => "_")
            for son_id in node.sons
                key_destine = replace(Alias.as_key(son_id), "." => "_")
                txt *= "  $key_origin -> $key_destine\n"
            end
        end
    end

    return txt
end

function main()
    println("╔════════════════════════════════════════╗")
    println("║  JULIA: Certificate Set Φ Visualization║")
    println("╚════════════════════════════════════════╝\n")

    # Load CNF
    cnf_path = "lean_project/simple_test.cnf"
    if !isfile(cnf_path)
        println("Error: $cnf_path not found")
        return
    end

    gmap = GraphMap.load_import!(cnf_path)
    println("📋 CNF: $(gmap.clausule_counter) clauses")

    # Run machine
    println("🤖 Running SatMachine to completion...")
    machine = SatMachine.new(gmap)
    SatMachine.init!(machine)
    SatMachine.run!(machine)

    finished = SatMachine.is_finished(machine)
    found_solution = SatMachine.have_solution(machine)
    current_step = machine.current_step

    println("✅ Execution done: step=$current_step, SAT=$found_solution")

    # Visualize
    println("\n🎨 Certificate Set (Φ) Analysis:")
    if found_solution
        # Get solution GPaths
        list_gpaths = SatMachine.get_gpath_solutions(machine)
        if !isempty(list_gpaths)
            gpath = first(list_gpaths)

            # Generate DOT
            dot_txt = build_diagram_dot(gpath)

            # Create output directory
            mkpath("./output")

            # Write DOT file
            dot_file = "./output/phi_final_julia.dot"
            open(dot_file, "w") do io
                print(io, dot_txt)
            end
            println("✅ Diagram exported to $dot_file")
            println("   (Render with: dot -Tpng $dot_file -o $(replace(dot_file, ".dot" => ".png")))")

            # Print statistics
            println("\n📊 Certificate Set Statistics:")
            println("  Current step: $(gpath.current_step)")
            total_nodes = 0
            for step in 0:(gpath.current_step-1)
                if haskey(gmap.table_lines.table, step)
                    line = gmap.table_lines.table[step]
                    count = length(line.table)
                    if count > 0
                        println("    Step $step: $count certificates")
                        total_nodes += count
                    end
                end
            end
            println("  Total nodes: $total_nodes")
        end
    else
        println("❌ Formula is UNSAT")
    end
end

main()
