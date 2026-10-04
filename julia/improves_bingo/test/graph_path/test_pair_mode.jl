# Pasos A1 y A3 del plan docs/plans/pair_mode.md, sobre el grafo de owners (plan
# docs/plans/graph_owners.md, F3).
#
# (A1) shares_every_step: simétrica, igual a la definición directa (en cada paso con línea en las dos
#      tablas hay un id común), y los casos límite (un paso solo en una tabla se ignora; un paso común
#      disjunto falla; una línea vacía común falla).
# (A3) Con PAIR_MODE :on, sobre los estados pinchados del lector (cada nodo del mapa de cada paso con
#      más de uno): tras clean + regla, toda arista comparte entrada en cada paso (PairOk) y el grafo
#      cumple sus invariantes; y el review completo da el mismo veredicto que con :off. Se cuentan (sin
#      exigir) los estados finales distintos. La simetría ya no se cuenta: es del grafo.

using Test

pair_nodes(gpath) = (ns = []; PathCollectionLines.for_each(gpath.table_lines, n -> push!(ns, n)); ns)

function pair_signature(gpath)
    ns = pair_nodes(gpath)
    return (Set(n.id for n in ns), GraphPath.alive_ids(gpath),
            Dict(n.id => (GraphPath.owners_table(gpath, n.id), Set(n.parents), Set(n.sons)) for n in ns))
end

# Aristas que no comparten entrada en algún paso común.
pair_bad(gpath) = count(e -> !GraphPath.shares_every_step(gpath.og, e.a, e.b), values(gpath.og.edges))

# La definición directa, sin atajos.
function shares_direct(og, x, w)
    tx, tw = og.inc[x], og.inc[w]
    all(step -> !haskey(tw, step) || !isempty(intersect(tx[step], tw[step])), keys(tx))
end

pid(step, index) = Alias.root_path_id((step = step, index = index))

# Un grafo con dos nodos x (paso 3) y w (paso 4), enlazados, y los vecinos que se pidan de los pasos
# 0..2. Los vecinos no se enlazan entre sí: solo cuentan las tablas de x y w.
function pair_graph(nx, nw; empty_w = Int[])
    og = PathOwnersGraph.new()
    for _ in 0:4
        PathOwnersGraph.add_step!(og)
    end
    x, w = pid(3, 0), pid(4, 0)
    ids = unique(vcat(nx, nw))
    for id in vcat(ids, [x, w])
        PathOwnersGraph.register!(og, id)
    end
    PathOwnersGraph.add_edge!(og, x, w)
    foreach(id -> PathOwnersGraph.add_edge!(og, x, id), nx)
    foreach(id -> PathOwnersGraph.add_edge!(og, w, id), nw)
    for step in empty_w                                        # línea presente y vacía en w
        get!(og.inc[w], step, SetPathNodesId())
    end
    return og, x, w
end

@testset "A1 shares_every_step" begin
    a = [pid(0, 0), pid(0, 1), pid(1, 0), pid(2, 1)]
    og, x, w = pair_graph(a, [pid(0, 1), pid(1, 0), pid(1, 1), pid(2, 1)])
    @test GraphPath.shares_every_step(og, x, w)
    @test GraphPath.shares_every_step(og, w, x)
    og, x, w = pair_graph(a, [pid(0, 0), pid(1, 1), pid(2, 1)])        # paso 1 disjunto
    @test !GraphPath.shares_every_step(og, x, w)
    @test !GraphPath.shares_every_step(og, w, x)
    og, x, w = pair_graph(a, [pid(0, 1), pid(2, 1)])                   # sin paso 1: se ignora
    @test GraphPath.shares_every_step(og, x, w)
    @test GraphPath.shares_every_step(og, w, x)
    og, x, w = pair_graph(a, [pid(0, 0), pid(1, 0)]; empty_w = [2])    # paso 2 vacío: común y disjunto
    @test !GraphPath.shares_every_step(og, x, w)
    @test !GraphPath.shares_every_step(og, w, x)

    # sobre grafos reales: simetría e igualdad con la definición directa
    n_pairs = 0; n_asym = 0; n_diff = 0; n_false = 0
    path = joinpath(@__DIR__, "../../test_window/instances/v5_c20_i1.cnf")
    machine = SatMachine.new(GraphMap.load_import!(path))
    redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    for gpath in SatMachine.get_gpath_list(machine)
        og = gpath.og
        ns = collect(keys(og.inc))
        for x in ns, w in ns
            n_pairs += 1
            s = GraphPath.shares_every_step(og, x, w)
            n_asym += s != GraphPath.shares_every_step(og, w, x)
            n_diff += s != shares_direct(og, x, w)
            n_false += !s
        end
    end
    println("shares_every_step: $n_pairs parejas, $n_false sin entrada común en algún paso, " *
            "$n_asym asimétricas, $n_diff distintas de la definición directa")
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
    n_states = 0; n_bad = 0; n_broken = 0; n_verdict = 0; n_diff_states = 0; n_fired = 0
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
                                n_broken += !PathOwnersGraph.check_invariants(g_on.og)
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
            "parejas malas tras la regla $n_bad, grafos que rompen invariantes $n_broken, " *
            "veredictos distintos $n_verdict, estados finales distintos $n_diff_states")
    @test n_states > 0
    @test n_bad == 0
    @test n_broken == 0
    @test n_verdict == 0
end
