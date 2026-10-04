# cleanInvalid sobre el grafo de owners (plan docs/plans/graph_owners.md, F3; antes, paso 3 del plan
# del v181, §6, en dos fases).
#
# Sobre estados REALES: los estados de la línea final de la máquina, pinchados como hace el lector
# (filter_require! de un id de mapa de un paso) y todavía sin review. Sobre una copia se aplica
# clean_invalid_nodes! y se comprueba:
#   (a) el grafo cumple sus invariantes (ningún id muerto en ninguna tabla, relación simétrica);
#   (b) los vivos del grafo son exactamente los nodos de table_lines;
#   (c) todos los nodos son válidos;
#   (d) aplicarla otra vez no cambia nada.
# La versión secuencial, el corte de la fase 2 e is_valid_intersect ya no existen: al quitar un nodo
# se van sus aristas.

using Test

function all_nodes(gpath)
    nodes = []
    PathCollectionLines.for_each(gpath.table_lines, n -> push!(nodes, n))
    return nodes
end

function signature(gpath)
    nodes = all_nodes(gpath)
    return (Set(n.id for n in nodes), GraphPath.alive_ids(gpath),
            Dict(n.id => (GraphPath.owners_table(gpath, n.id), Set(n.parents), Set(n.sons)) for n in nodes))
end

alive_are_nodes(gpath) = GraphPath.alive_ids(gpath) == Set(n.id for n in all_nodes(gpath))

nodes_valid(gpath) = all(n -> GraphPath.is_valid_node(gpath, n), all_nodes(gpath))

function pinned_states(path)
    gmap = GraphMap.load_import!(path)
    machine = SatMachine.new(gmap)
    SatMachine.run!(machine)
    states = []
    for gpath in SatMachine.get_gpath_list(machine)
        for step in 0:gpath.current_step-1
            ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
            map_ids = unique([pid.id for pid in ids])
            length(map_ids) < 2 && continue
            for x in map_ids
                g = deepcopy(gpath)
                GraphPath.filter_require!(g, x)
                push!(states, g)
            end
        end
    end
    return states
end

const CLEAN_CASES = [
    "../example_cnf/rand3sat_v4_c20.cnf",
    "../example_cnf/rand3sat_v8_c10.cnf",
    "../../test_window/instances/v5_c20_i1.cnf",
    "../../test_window/instances/v6_c26_i1.cnf",
]

@testset "cleanInvalid sobre el grafo de owners" begin
    n_states = 0
    n_valid = 0
    for rel in CLEAN_CASES
        path = joinpath(@__DIR__, rel)
        for g0 in pinned_states(path)
            n_states += 1
            @test PathOwnersGraph.check_invariants(g0.og)
            g2 = deepcopy(g0)
            GraphPath.clean_invalid_nodes!(g2)
            @test PathOwnersGraph.check_invariants(g2.og)
            if g2.is_valid && g2.table_lines.is_valid
                n_valid += 1
                @test alive_are_nodes(g2)
                @test nodes_valid(g2)
                g3 = deepcopy(g2)
                GraphPath.clean_invalid_nodes!(g3)
                @test signature(g3) == signature(g2)
            end
        end
    end
    println("cleanInvalid: estados pinchados $n_states, válidos tras la purga $n_valid")
    @test n_states > 0
    @test n_valid > 0
end
