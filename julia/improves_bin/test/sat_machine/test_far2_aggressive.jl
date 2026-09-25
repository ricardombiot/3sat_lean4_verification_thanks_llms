using Test
using Main.AbsSat.Alias
using Main.AbsSat.GraphMap
using Main.AbsSat.SatMachine
using Main.AbsSat.DBDocuments.PathDocumentOwners
using Main.AbsSat.DBDocuments.PathDocumentNode
using Main.AbsSat.DBCollections.PathCollectionLines
using Main.AbsSat.DBCollections.PathCollectionNodes
# ============================================================================
# TEST: far2 (fórmula con owners incompatibles)
# ============================================================================

function test_far2_aggressive()
    println("\n" * "="^80)
    println("TEST: far2 (fórmula con incompatibilidades)")
    println("="^80)

    # Cargar far2.cnf
    cnf_path = "/tmp/far2.cnf"

    if !isfile(cnf_path)
        println("✗ Archivo $cnf_path no encontrado")
        return
    end

    println("✓ Cargando $cnf_path...")

    # Leer CNF y crear GMap
    gmap = GraphMap.load_import!(cnf_path)

    println("✓ GMap creado: $(gmap.step) pasos")

    # ===== PRUEBA 1: Review ESTÁNDAR =====
    println("\n[1] Ejecutando review ESTÁNDAR...")
    machine_std = SatMachine.new(gmap)
    time_std = @elapsed SatMachine.run!(machine_std)

    entries_std = 0
    nodos_std = 0
    paths_std = length(SatMachine.get_gpath_list(machine_std))

    for gpath in SatMachine.get_gpath_list(machine_std)
        # Contar entradas y nodos
        for step in 0:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                if PathDocumentNode.is_valid(path_node)
                    nodos_std += 1
                end
                owners_at_step = PathDocumentOwners.get(path_node.owners, step)
                if owners_at_step != nothing
                    entries_std += length(owners_at_step)
                end
                return false
            end)
        end
    end

    has_solution_std = SatMachine.have_solution(machine_std)
    println("   Tiempo: $(round(time_std, digits=4)) s")
    println("   Solución: $has_solution_std")
    println("   Caminos: $paths_std")
    println("   Entradas totales: $entries_std")
    println("   Nodos válidos: $nodos_std")

    # ===== PRUEBA 2: Review AGRESIVO =====
    println("\n[2] Ejecutando review AGRESIVO...")

    # Re-crear GMap (el anterior fue modificado por run!)
    gmap_agg = GraphMap.load_import!(cnf_path)

    machine_agg = SatMachine.new(gmap_agg)

    time_agg = @elapsed begin
        SatMachine.run!(machine_agg)

        # Post-procesamiento: aplicar review agresivo
        for gpath in SatMachine.get_gpath_list(machine_agg)
            if !gpath.is_valid
                continue
            end

            gpath.review_owners = false
            iteration = 0

            while gpath.is_valid && gpath.review_owners && iteration < 100
                iteration += 1
                gpath.review_owners = false

                for step in 0:gpath.current_step-1
                    col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
                    PathCollectionNodes.filter!(col_nodes, function (node_x)
                        if !PathDocumentNode.is_valid(node_x)
                            return false
                        end

                        owners_snapshot = collect(
                            PathDocumentOwners.get(node_x.owners, step)
                            |> (s -> s != nothing ? collect(s) : [])
                        )

                        for owner_id in owners_snapshot
                            owner_w = PathCollectionLines.get_node(
                                gpath.table_lines, owner_id
                            )

                            if owner_w == nothing
                                continue
                            end

                            owners_intersection = deepcopy(node_x.owners)
                            PathDocumentOwners.intersect!(
                                owners_intersection, owner_w.owners
                            )

                            if !PathDocumentOwners.is_valid(owners_intersection)
                                PathDocumentOwners.remove!(node_x.owners, owner_id)
                                gpath.review_owners = true
                            end
                        end

                        return !PathDocumentNode.is_valid(node_x)
                    end)

                    PathCollectionLines.check_if_valid_line!(gpath.table_lines, step)
                    check_if_graph_valid!(gpath)

                    if !gpath.is_valid
                        break
                    end
                end
            end
        end
    end

    entries_agg = 0
    nodos_agg = 0
    paths_agg = length(SatMachine.get_gpath_list(machine_agg))

    for gpath in SatMachine.get_gpath_list(machine_agg)
        for step in 0:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                if PathDocumentNode.is_valid(path_node)
                    nodos_agg += 1
                end
                owners_at_step = PathDocumentOwners.get(path_node.owners, step)
                if owners_at_step != nothing
                    entries_agg += length(owners_at_step)
                end
                return false
            end)
        end
    end

    has_solution_agg = SatMachine.have_solution(machine_agg)
    println("   Tiempo: $(round(time_agg, digits=4)) s")
    println("   Solución: $has_solution_agg")
    println("   Caminos: $paths_agg")
    println("   Entradas totales: $entries_agg")
    println("   Nodos válidos: $nodos_agg")

    # ===== COMPARATIVA =====
    println("\n[COMPARATIVA]")
    println("   Entradas quitadas: $(entries_std - entries_agg) ($(round(100*(entries_std-entries_agg)/max(entries_std,1), digits=2))%)")
    println("   Nodos perdidos: $(nodos_std - nodos_agg)")

    overhead = round(100*(time_agg - time_std)/time_std, digits=2)
    println("   Overhead de tiempo: $overhead%")

    # ===== VALIDACIÓN =====
    println("\n[VALIDACIÓN]")
    @test has_solution_std == has_solution_agg
    @test nodos_agg <= nodos_std

    if entries_agg < entries_std
        println("   ✓ Agresivo quitó $(entries_std - entries_agg) entries incompatibles!")
    elseif entries_agg == entries_std
        println("   ⚠ Agresivo NO encontró incompatibilidades (todas las entries son compatibles)")
    else
        println("   ✗ ERROR: Agresivo agregó entries")
    end

    return (entries_std, entries_agg, time_std, time_agg)
end

@testset "FarTwoAggressive" begin
    test_far2_aggressive()
end
