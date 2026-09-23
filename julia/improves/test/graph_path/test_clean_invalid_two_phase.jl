# Paso 3 del plan del v181, §6: el cleanInvalid en dos fases.
#
# Sobre estados REALES: los estados de la línea final de la máquina, pinchados como hace el lector
# (filter_require! de un id de mapa de un paso) y todavía sin review. Sobre copias se aplican las dos
# versiones de cleanInvalid y se comprueba, para la de dos fases:
#   (a) ninguna tabla de nodo guarda un id que no esté en la global;
#   (b) toda entrada de la global es un nodo presente;
#   (c) todos los nodos son válidos;
#   (d) aplicarla otra vez no cambia nada.
# Y se cuenta cuántas veces la secuencial deja ids fuera de la global en alguna tabla (la dependencia
# del orden que el cambio elimina).

using Test

function all_nodes(gpath)
    nodes = []
    PathCollectionLines.for_each(gpath.table_lines, n -> push!(nodes, n))
    return nodes
end

owner_entries(owners) = [id for (step, set) in owners.table for id in set]

function signature(gpath)
    nodes = all_nodes(gpath)
    return (Set(n.id for n in nodes), Set(owner_entries(gpath.owners)),
            Dict(n.id => (Set(owner_entries(n.owners)), Set(n.parents), Set(n.sons)) for n in nodes))
end

tables_inside_global(gpath) =
    all(n -> all(id -> PathDocumentOwners.is_owner(gpath.owners, id), owner_entries(n.owners)), all_nodes(gpath))

global_are_nodes(gpath) =
    all(id -> PathCollectionLines.get_node(gpath.table_lines, id) !== nothing, owner_entries(gpath.owners))

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

@testset "cleanInvalid en dos fases" begin
    n_states = 0
    n_seq_dead = 0
    for rel in CLEAN_CASES
        path = joinpath(@__DIR__, rel)
        for g0 in pinned_states(path)
            n_states += 1
            g_seq = deepcopy(g0)
            GraphPath.clean_invalid_nodes_sequential!(g_seq)
            if g_seq.is_valid && !tables_inside_global(g_seq)
                n_seq_dead += 1
            end

            g2 = deepcopy(g0)
            GraphPath.clean_invalid_nodes_two_phase!(g2)
            if g2.is_valid
                @test tables_inside_global(g2)
                @test global_are_nodes(g2)
                @test nodes_valid(g2)
                g3 = deepcopy(g2)
                GraphPath.clean_invalid_nodes_two_phase!(g3)
                @test signature(g3) == signature(g2)
            end
        end
    end
    println("cleanInvalid: estados pinchados $n_states; la secuencial deja ids fuera de la global en $n_seq_dead")
    @test n_states > 0
end
