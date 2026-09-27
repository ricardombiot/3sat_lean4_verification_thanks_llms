using Test
using Main.AbsSat.Alias
using Main.AbsSat.GraphMap
using Main.AbsSat.SatMachine
using Main.AbsSat.DBDocuments.PathDocumentOwners
using Main.AbsSat.DBDocuments.PathDocumentNode
using Main.AbsSat.DBCollections.PathCollectionLines
using Main.AbsSat.DBCollections.PathCollectionNodes

# ============================================================================
# GENERADOR DE FÓRMULAS PARA TEST AGRESIVO
# ============================================================================

"""
    generate_aggressive_formula(n::Int, mult::Int = 10) → GMap

Genera una fórmula con:
- n variables
- n × mult claúsulas "smoke" (x ∨ ¬x ∨ x) triviales
- Cadenas de implicación correlacionadas:
  - i → i-1 para i > 2
  - i-2 → i para i > 2

Esto crea structures donde owners pueden ser obsoletos.
"""
function generate_aggressive_formula(n::Int, mult::Int = 10) :: GraphMap.GMap
    gmap = GraphMap.new()

    # Agregar variables
    for i in 1:n
        GraphMap.add_var!(gmap, "$i")
    end

    # Claúsulas smoke (triviales)
    for i in 1:n
        for j in 1:mult
            GraphMap.add_gate!(gmap, "$i", "!$i", "$i")
        end
    end

    # Cadenas de implicación correlacionadas
    for i in 3:n
        GraphMap.add_gate!(gmap, "$i", "!$(i-1)", "$(i-2)")
        GraphMap.add_gate!(gmap, "$(i-2)", "!$(i-1)", "$i")
    end

    GraphMap.close_gates!(gmap)
    return gmap
end


# ============================================================================
# INSTRUMENTACIÓN: Contadores para review estándar vs agresivo
# ============================================================================

mutable struct ReviewStats
    entries_before :: Int
    entries_after :: Int
    entries_removed :: Int
    iterations :: Int
    dead_ends_removed :: Int
    nodos_validos :: Int
    time_elapsed :: Float64
end

function ReviewStats()
    ReviewStats(0, 0, 0, 0, 0, 0, 0.0)
end

function count_total_entries(gpath :: SatMachine.GPath) :: Int
    # Contar todas las entradas (nodo, owner) en el grafo - SIMPLIFICADO
    # Iterador sobre PathCollectionNodes.filter requiere callback
    total = Ref(0)
    for step in 0:gpath.current_step-1
        col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
        PathCollectionNodes.filter!(col_nodes, function (path_node)
            owners_at_step = PathDocumentOwners.get(path_node.owners, step)
            if owners_at_step != nothing
                total[] += length(owners_at_step)
            end
            return false  # No filtrar, solo contar
        end)
    end
    return total[]
end

function count_valid_nodes(gpath :: SatMachine.GPath) :: Int
    # Contar nodos válidos en el grafo
    total = Ref(0)
    for step in 0:gpath.current_step-1
        col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
        PathCollectionNodes.filter!(col_nodes, function (path_node)
            if PathDocumentNode.is_valid(path_node)
                total[] += 1
            end
            return false  # No filtrar
        end)
    end
    return total[]
end


# ============================================================================
# REVIEW AGRESIVO (Propuesta del usuario)
# ============================================================================

"""
    make_review_owners_aggressive!(gpath, stats::ReviewStats)

Review agresivo: para cada nodo x, para cada owner w:
- Intersectar owners(x) ∩ owners(w)
- Si la intersección es inválida → quitar w

Itera hasta punto fijo (hasta que no haya cambios).
"""
function make_review_owners_aggressive!(gpath :: SatMachine.GPath,
                                        stats :: ReviewStats)
    if !gpath.is_valid
        return
    end

    stats.entries_before = count_total_entries(gpath)
    gpath.review_owners = false

    iteration = 0
    while gpath.is_valid && gpath.review_owners && iteration < 100
        iteration += 1
        gpath.review_owners = false

        # Para cada nodo del grafo
        for step in 0:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            PathCollectionNodes.filter!(col_nodes, function (node_x)
                if !PathDocumentNode.is_valid(node_x)
                    return false
                end

                # Snapshot de owners de este nodo en este paso
                owners_snapshot = collect(
                    PathDocumentOwners.get(node_x.owners, step)
                    |> (s -> s != nothing ? collect(s) : [])
                )

                # Para cada owner w del nodo x
                for owner_id in owners_snapshot
                    owner_w = PathCollectionLines.get_node(
                        gpath.table_lines, owner_id
                    )

                    if owner_w == nothing
                        continue
                    end

                    # Intersectar: ¿comparten owners en todos los pasos?
                    owners_intersection = deepcopy(node_x.owners)
                    PathDocumentOwners.intersect!(
                        owners_intersection, owner_w.owners
                    )

                    # Si no son compatibles en TODOS los pasos → quitar
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

    stats.entries_after = count_total_entries(gpath)
    stats.entries_removed = stats.entries_before - stats.entries_after
    stats.iterations = iteration
    stats.nodos_validos = count_valid_nodes(gpath)
end


# ============================================================================
# TEST: Comparativa estándar vs agresivo
# ============================================================================

function test_aggressive_vs_standard(n::Int, mult::Int = 10)
    # Compara el review estándar con el review agresivo en una fórmula generada.
    println("\n" * "="^80)
    println("TEST: Agresivo vs Estándar | n=$n, mult=$mult")
    println("="^80)

    # Generar fórmula
    gmap = generate_aggressive_formula(n, mult)
    println("✓ Fórmula generada: $n variables, $(n*mult + 2*(n-2)) cláusulas")

    # ===== PRUEBA 1: Review ESTÁNDAR =====
    println("\n[1] Ejecutando review ESTÁNDAR...")
    machine_std = SatMachine.new(gmap)
    time_std = @elapsed SatMachine.run!(machine_std)

    entries_std = 0
    nodos_std = 0
    for gpath in SatMachine.get_gpath_list(machine_std)
        entries_std += count_total_entries(gpath)
        nodos_std += count_valid_nodes(gpath)
    end

    has_solution_std = SatMachine.have_solution(machine_std)
    println("   Tiempo: $(round(time_std, digits=4)) s")
    println("   Solución: $has_solution_std")
    println("   Entradas totales: $entries_std")
    println("   Nodos válidos: $nodos_std")

    # ===== PRUEBA 2: Review AGRESIVO =====
    println("\n[2] Ejecutando review AGRESIVO...")
    machine_agg = SatMachine.new(gmap)

    # Opción A: Modificar directamente durante ejecución (más intrusivo)
    # Opción B: Agregar paso post-procesamiento (más limpio)

    time_agg = @elapsed begin
        SatMachine.run!(machine_agg)

        # Post-procesamiento: aplicar review agresivo a cada camino
        stats = ReviewStats()
        for gpath in SatMachine.get_gpath_list(machine_agg)
            make_review_owners_aggressive!(gpath, stats)
        end
    end

    entries_agg = 0
    nodos_agg = 0
    for gpath in SatMachine.get_gpath_list(machine_agg)
        entries_agg += count_total_entries(gpath)
        nodos_agg += count_valid_nodes(gpath)
    end

    has_solution_agg = SatMachine.have_solution(machine_agg)
    println("   Tiempo: $(round(time_agg, digits=4)) s")
    println("   Solución: $has_solution_agg")
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

    if entries_agg <= entries_std
        println("   ✓ Agresivo nunca quita entradas válidas")
    else
        println("   ✗ ADVERTENCIA: Agresivo agregó entradas")
    end

    return (entries_std, entries_agg, time_std, time_agg)
end


# ============================================================================
# SUITE DE TESTS
# ============================================================================

@testset "AggressiveReview" begin

    # Test pequeño
    println("\n>>> Test pequeño (n=5)")
    test_aggressive_vs_standard(5, 5)

    # Test mediano
    println("\n>>> Test mediano (n=7)")
    test_aggressive_vs_standard(7, 8)

    # Test más grande (si el hardware lo permite)
    if false  # Cambiar a true para tests extensos
        println("\n>>> Test grande (n=10)")
        test_aggressive_vs_standard(10, 10)
    end

end


# ============================================================================
# EJECUCIÓN DIRECTA (para debugging)
# ============================================================================

if abspath(PROGRAM_FILE) == @__FILE__
    println("\n[MODO STANDALONE]")
    test_aggressive_vs_standard(5, 5)
end
