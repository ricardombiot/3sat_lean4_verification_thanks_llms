# Pasos A1 y A3 del plan docs/plans/pair_mode.md: la regla de parejas tras la limpieza.
#
# (A1) shares_every_step: simétrica, igual a intersect! + is_valid sobre una copia (con el mismo
#      max_step), y los casos límite (un paso solo en una tabla se ignora; un paso común disjunto falla).
# (A3) Con PAIR_MODE :on, sobre los estados pinchados del lector (cada nodo del mapa de cada paso con
#      más de uno): tras clean + regla, toda pareja mutua viva comparte entrada en cada paso (PairOk),
#      la simetría se conserva y ninguna pareja se compara con max_step distinto; y el review completo
#      da el mismo veredicto que con :off. Se cuentan (sin exigir) los estados finales distintos.

using Test

pair_nodes(gpath) = (ns = []; PathCollectionLines.for_each(gpath.table_lines, n -> push!(ns, n)); ns)
pair_entries(owners) = [id for (step, set) in owners.table for id in set]

function pair_signature(gpath)
    ns = pair_nodes(gpath)
    return (Set(n.id for n in ns), Set(pair_entries(gpath.owners)),
            Dict(n.id => (Set(pair_entries(n.owners)), Set(n.parents), Set(n.sons)) for n in ns))
end

# Parejas vivas que se poseen y no comparten entrada en algún paso común.
function pair_bad(gpath)
    n = 0
    for x in pair_nodes(gpath), wid in pair_entries(x.owners)
        wid == x.id && continue
        w = PathCollectionLines.get_node(gpath.table_lines, wid)
        w === nothing && continue
        n += !PathDocumentOwners.shares_every_step(x.owners, w.owners)
    end
    return n
end

# Parejas vivas asimétricas: w ∈ owners(x), w vivo, x ∉ owners(w).
function pair_asym(gpath)
    n = 0
    for x in pair_nodes(gpath), wid in pair_entries(x.owners)
        wid == x.id && continue
        w = PathCollectionLines.get_node(gpath.table_lines, wid)
        w === nothing && continue
        n += !PathDocumentOwners.is_owner(w.owners, x.id)
    end
    return n
end

# El test de pareja por la vía de siempre: cortar una copia y mirar si queda válida.
function shares_by_intersect(a, b)
    c = deepcopy(a)
    PathDocumentOwners.intersect!(c, b)
    return PathDocumentOwners.is_valid(c)
end

pid(step, index) = Alias.root_path_id((step = step, index = index))

function owners_of(ids...)
    o = PathDocumentOwners.new()
    for id in ids
        PathDocumentOwners.insert!(o, id)
    end
    return o
end

@testset "A1 shares_every_step" begin
    # casos a mano
    a = owners_of(pid(0, 0), pid(0, 1), pid(1, 0), pid(2, 1))
    b = owners_of(pid(0, 1), pid(1, 0), pid(1, 1), pid(2, 1))
    @test PathDocumentOwners.shares_every_step(a, b)
    @test PathDocumentOwners.shares_every_step(b, a)
    c = owners_of(pid(0, 0), pid(1, 1), pid(2, 1))          # paso 1 disjunto con a
    @test !PathDocumentOwners.shares_every_step(a, c)
    @test !PathDocumentOwners.shares_every_step(c, a)
    d = owners_of(pid(0, 1), pid(2, 1))                     # sin paso 1: se ignora
    @test PathDocumentOwners.shares_every_step(a, d)
    @test PathDocumentOwners.shares_every_step(d, a)
    e = owners_of(pid(0, 0), pid(1, 0))
    PathDocumentOwners.create_owners_line!(e, 2)            # paso 2 vacío: común y disjunto
    @test !PathDocumentOwners.shares_every_step(a, e)
    @test !PathDocumentOwners.shares_every_step(e, a)

    # sobre tablas reales: simetría e igualdad con intersect! + is_valid
    n_pairs = 0; n_asym = 0; n_diff = 0; n_false = 0
    path = joinpath(@__DIR__, "../../test_window/instances/v5_c20_i1.cnf")
    machine = SatMachine.new(GraphMap.load_import!(path))
    redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    for gpath in SatMachine.get_gpath_list(machine)
        ns = pair_nodes(gpath)
        for x in ns, w in ns
            x.owners.max_step == w.owners.max_step || continue
            n_pairs += 1
            s = PathDocumentOwners.shares_every_step(x.owners, w.owners)
            n_asym += s != PathDocumentOwners.shares_every_step(w.owners, x.owners)
            PathDocumentOwners.is_valid(x.owners) || continue
            n_diff += s != shares_by_intersect(x.owners, w.owners)
            n_false += !s
        end
    end
    println("shares_every_step: $n_pairs parejas, $n_false sin entrada común en algún paso, " *
            "$n_asym asimétricas, $n_diff distintas de intersect!")
    @test n_pairs > 0
    @test n_false > 0
    @test n_asym == 0
    @test n_diff == 0
end

const PAIR_CASES = [
    "../example_cnf/rand3sat_v4_c20.cnf",
    "../example_cnf/rand3sat_v8_c10.cnf",
    "../../test_window/instances/v5_c20_i1.cnf",
]

@testset "A3 regla de parejas" begin
    old_mode = GraphPath.PAIR_MODE[]
    n_states = 0; n_bad = 0; n_asym = 0; n_verdict = 0; n_diff_states = 0; n_fired = 0
    GraphPath.PAIR_MAXSTEP[] = 0
    try
        for rel in PAIR_CASES
            path = joinpath(@__DIR__, rel)
            GraphPath.PAIR_MODE[] = :off
            machine = SatMachine.new(GraphMap.load_import!(path))
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            for gpath in SatMachine.get_gpath_list(machine)
                for step in 0:gpath.current_step-1
                    ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
                    map_ids = unique([p.id for p in ids])
                    length(map_ids) < 2 && continue
                    for x in map_ids
                        pinned = deepcopy(gpath)
                        GraphPath.filter_require!(pinned, x)
                        n_states += 1

                        # :off, el review de siempre
                        GraphPath.PAIR_MODE[] = :off
                        g_off = deepcopy(pinned)
                        redirect_stdout(devnull) do
                            GraphPath.make_review_owners!(g_off)
                        end

                        # :on, mirando el estado justo después de clean + regla
                        GraphPath.PAIR_MODE[] = :on
                        g_on = deepcopy(pinned)
                        if pinned.review_owners && pinned.is_valid
                            removed0 = GraphPath.PAIR_REMOVED[]
                            redirect_stdout(devnull) do
                                GraphPath.clean_invalid_nodes!(g_on)
                                GraphPath.pair_consistency_after_clean!(g_on)
                            end
                            n_fired += GraphPath.PAIR_REMOVED[] > removed0
                            if g_on.is_valid && g_on.table_lines.is_valid
                                n_bad += pair_bad(g_on)
                                n_asym += pair_asym(g_on)
                            end
                            g_on.review_owners = true
                        end
                        redirect_stdout(devnull) do
                            GraphPath.make_review_owners!(g_on)
                        end

                        n_verdict += g_off.is_valid != g_on.is_valid
                        if g_off.is_valid && g_on.is_valid
                            n_diff_states += pair_signature(g_off) != pair_signature(g_on)
                        end
                    end
                end
            end
        end
    finally
        GraphPath.PAIR_MODE[] = old_mode
    end
    println("regla de parejas: $n_states estados pinchados, la regla actúa en $n_fired, " *
            "parejas malas tras la regla $n_bad, asimétricas $n_asym, max_step distinto " *
            "$(GraphPath.PAIR_MAXSTEP[]), veredictos distintos $n_verdict, estados finales distintos $n_diff_states")
    @test n_states > 0
    @test n_bad == 0
    @test n_asym == 0
    @test GraphPath.PAIR_MAXSTEP[] == 0
    @test n_verdict == 0
end
