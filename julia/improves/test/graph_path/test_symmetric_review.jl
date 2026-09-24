# Paso A4 del plan docs/plans/review_simetrico.md: el review simétrico (SYM_MODE :on).
#
# (1) intersect_removed! corta igual que intersect! y devuelve exactamente lo que quita.
# (2) Con :on, sobre los estados de la máquina y del lector (línea final pinchada y revisada):
#     simetría entre nodos vivos tras cada etapa del review, la rama «asymmetric» del filtro
#     agresivo no se dispara, el corte de clean no quita ids de nodos vivos, y el review es
#     idempotente. Se cuentan (sin exigir nada) los nodos eliminados en las pasadas.

using Test

sym_nodes(gpath) = (ns = []; PathCollectionLines.for_each(gpath.table_lines, n -> push!(ns, n)); ns)
sym_entries(owners) = [id for (step, set) in owners.table for id in set]

function sym_signature(gpath)
    ns = sym_nodes(gpath)
    return (Set(n.id for n in ns), Set(sym_entries(gpath.owners)),
            Dict(n.id => (Set(sym_entries(n.owners)), Set(n.parents), Set(n.sons)) for n in ns))
end

# Parejas vivas asimétricas: w ∈ owners(x), w vivo, x ∉ owners(w).
function sym_asym(gpath)
    n = 0
    for x in sym_nodes(gpath), wid in sym_entries(x.owners)
        wid == x.id && continue
        w = PathCollectionLines.get_node(gpath.table_lines, wid)
        w === nothing && continue
        n += !PathDocumentOwners.is_owner(w.owners, x.id)
    end
    return n
end

# Una vuelta como make_review_owners!, mirando la simetría tras cada etapa.
function sym_review!(gpath, stats)
    if gpath.is_valid && gpath.review_owners
        gpath.review_owners = false
        GraphPath.clean_invalid_nodes!(gpath)
        gpath.is_valid && (stats[:asym] += sym_asym(gpath))
        n0 = length(sym_nodes(gpath))
        GraphPath.review_owners_parents_sons!(gpath)
        gpath.is_valid && (stats[:asym] += sym_asym(gpath))
        GraphPath.review_owners_sons_parents!(gpath)
        gpath.is_valid && (stats[:asym] += sym_asym(gpath))
        stats[:removed_pass] += n0 - length(sym_nodes(gpath))
        GraphPath.agressive_consistence_filter!(gpath)
        gpath.is_valid && (stats[:asym] += sym_asym(gpath))
        GraphPath.chain_consistence_filter!(gpath)
        gpath.is_valid && (stats[:asym] += sym_asym(gpath))
        gpath.review_owners && sym_review!(gpath, stats)
    end
end

const SYM_CASES = [
    "../example_cnf/rand3sat_v4_c20.cnf",
    "../example_cnf/rand3sat_v8_c10.cnf",
    "../../test_window/instances/v5_c20_i1.cnf",
    "../../test_window/instances/v6_c26_i1.cnf",
]

@testset "review simétrico" begin
    old_mode = GraphPath.SYM_MODE[]
    GraphPath.SYM_MODE[] = :on
    GraphPath.AGG_ASYM[] = 0
    GraphPath.CLEAN_CUT_LIVE[] = 0
    stats = Dict(:asym => 0, :removed_pass => 0)
    n_states = 0; n_cut_checked = 0; n_cut_bad = 0
    try
        for rel in SYM_CASES
            path = joinpath(@__DIR__, rel)
            gmap = GraphMap.load_import!(path)
            machine = SatMachine.new(gmap)
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            for gpath in SatMachine.get_gpath_list(machine)
                @test sym_asym(gpath) == 0
                # (1) intersect_removed! frente a intersect!, con la tabla de cada nodo y la de su padre
                for n in sym_nodes(gpath), pid in n.parents
                    p = PathCollectionLines.get_node(gpath.table_lines, pid)
                    a = deepcopy(n.owners); b = deepcopy(n.owners)
                    PathDocumentOwners.intersect!(a, p.owners)
                    removed = PathDocumentOwners.intersect_removed!(b, p.owners)
                    n_cut_checked += 1
                    n_cut_bad += !(sym_entries(a) ⊆ sym_entries(b) && sym_entries(b) ⊆ sym_entries(a) &&
                                   PathDocumentOwners.is_valid(a) == PathDocumentOwners.is_valid(b) &&
                                   Set(removed) == setdiff(Set(sym_entries(n.owners)), Set(sym_entries(b))) &&
                                   length(removed) == length(Set(removed)))
                end
                # (2) estados del lector
                for step in 0:gpath.current_step-1
                    ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
                    map_ids = unique([pid.id for pid in ids])
                    length(map_ids) < 2 && continue
                    for x in map_ids
                        g = deepcopy(gpath)
                        GraphPath.filter_require!(g, x)
                        redirect_stdout(devnull) do
                            sym_review!(g, stats)
                        end
                        n_states += 1
                        if g.is_valid
                            g2 = deepcopy(g)
                            g2.review_owners = true
                            redirect_stdout(devnull) do
                                GraphPath.make_review_owners!(g2)
                            end
                            @test sym_signature(g2) == sym_signature(g)
                        end
                    end
                end
            end
        end
    finally
        GraphPath.SYM_MODE[] = old_mode
    end
    println("review simétrico: $n_states estados del lector, parejas asimétricas $(stats[:asym]), " *
            "rama asimétrica del agresivo $(GraphPath.AGG_ASYM[]), ids vivos cortados por clean " *
            "$(GraphPath.CLEAN_CUT_LIVE[]), nodos eliminados en las pasadas $(stats[:removed_pass]); " *
            "intersect_removed! $n_cut_checked cortes, $n_cut_bad distintos")
    @test n_states > 0
    @test stats[:asym] == 0
    @test GraphPath.AGG_ASYM[] == 0
    @test GraphPath.CLEAN_CUT_LIVE[] == 0
    @test n_cut_bad == 0
end
