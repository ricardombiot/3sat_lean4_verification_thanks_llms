# PinStable y la conmutación filtro/UP (30-sept-2026, rama reader-stuck; lean LiveUp.lean, PinLive).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_pinstable.jl <salida.tsv> [muestras]
#
# Con FORBID = :on. Para cada envío de la máquina (remitente g antes del filtro, requisitos reqs, destino d):
#   ps_*   — PinStable: LiveExt tras fijar un conjunto al azar de 1–3 nodos de mapa (pasos al azar) en g;
#            states (válidos), dead (callejones), dead_states.
#   com_*  — la conmutación: A = filtro(up(filtro(g, reqs)), R) y B = up(filtro(g, reqs ∪ R)), con R pins al azar por
#            debajo de la cima de g. runs, valid_diff (uno válido y el otro no), alive_diff, edge_diff, forbid_diff
#            (entre los válidos), docs_diff (padres vivos de los documentos vivos); con los mismos vivos y aristas,
#            triBA / triAB (tríos sobre un triángulo prohibidos en B y no en A, y al revés) y deadA (callejones de
#            LiveExt en A, la llegada fijada).
# LiveExt como en probe_liveext.jl: cadenas vivas de la cima abajo por padres, sin trío prohibido.

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 4
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20260930))
const SENDS = Any[]

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.is_valid && push!($(SENDS), (deepcopy(gpath), copy(requires), map_id_node, title, prohibited))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b || PG.has_edge(g.og, a, b)
dead(g, a, b, r) = length(unique((a, b, r))) == 3 && PG.dead_trio(g.og, a, b, r)

function live_parents(g, x, chain)
    nd = PathCollectionLines.get_node(g.table_lines, x)
    nd === nothing && return PathNodeId[]
    [p for p in nd.parents if PG.is_alive(g.og, p) && all(w -> adj(g, w, p), chain) &&
        !any(dead(g, chain[i], chain[j], p) for i in eachindex(chain) for j in i+1:length(chain))]
end

# callejones de LiveExt en g
function dead_ends(g)
    top = Int(g.current_step) - 1
    leaves = Ref(0); deads = Ref(0)
    chain = PathNodeId[]
    function dfs(x)
        leaves[] > CAP && return
        push!(chain, x)
        if Int(x.id.step) == 0
            leaves[] += 1
        else
            ps = live_parents(g, x, chain)
            isempty(ps) ? (deads[] += 1) : foreach(dfs, ps)
        end
        pop!(chain)
    end
    foreach(dfs, alive_at(g, top))
    return deads[]
end

# pins al azar: nodos de mapa de pasos con dos ids vivos, por debajo de `maxstep`
function random_pins(g, maxstep, n)
    steps = [s for s in 1:maxstep if length(unique(x.id for x in alive_at(g, s))) >= 2]
    isempty(steps) && return NodeId[]
    pins = NodeId[]
    for s in shuffle(RNG[], steps)[1:min(n, length(steps))]
        ids = unique(x.id for x in alive_at(g, s))
        push!(pins, ids[rand(RNG[], 1:length(ids))])
    end
    return pins
end

function docs(g)
    al = Set(x for (_, xs) in g.og.alive for x in xs)
    Set((x, sort([p for p in PathCollectionLines.get_node(g.table_lines, x).parents if p in al], by = string))
        for x in al if PathCollectionLines.get_node(g.table_lines, x) !== nothing)
end
fingerprint(g) = (Set(x for (_, xs) in g.og.alive for x in xs), Set(keys(g.og.edges)),
                  Set((k, sort(collect(e.forbid), by = string)) for (k, e) in g.og.edges if !isempty(e.forbid)),
                  docs(g))

function judge(send)
    (g0, reqs, d, title, proh) = send
    top = Int(g0.current_step) - 1
    for _ in 1:SAMPLES
        # PinStable
        R = random_pins(g0, top, rand(RNG[], 1:3))
        g = deepcopy(g0)
        GraphPath.filter!(g, SetNodesId(R))
        if g.is_valid
            bump(:ps_states)
            k = dead_ends(g)
            bump(:ps_dead, k); k > 0 && bump(:ps_dead_states)
        end
        # conmutación
        R2 = random_pins(g0, top, rand(RNG[], 1:2))
        isempty(R2) && continue
        bump(:com_runs)
        A = deepcopy(g0)
        GraphPath.filter!(A, reqs); GraphPath.do_up!(A, d, title, proh)
        A.is_valid && GraphPath.filter!(A, SetNodesId(R2))
        B = deepcopy(g0)
        GraphPath.filter!(B, union(reqs, SetNodesId(R2))); GraphPath.do_up!(B, d, title, proh)
        if A.is_valid != B.is_valid
            bump(:com_valid_diff)
        elseif A.is_valid
            fa, fb = fingerprint(A), fingerprint(B)
            fa[1] == fb[1] || bump(:com_alive_diff)
            fa[2] == fb[2] || bump(:com_edge_diff)
            fa[3] == fb[3] || bump(:com_forbid_diff)
            fa[4] == fb[4] || bump(:com_docs_diff)
            # tríos en triángulos comunes: prohibidos en uno y no en el otro
            if fa[1] == fb[1] && fa[2] == fb[2]
                for (k, e) in A.og.edges, r in collect(PG.neighbors_all(A.og, e.a))
                    (r == e.a || r == e.b || !PG.has_edge(A.og, e.b, r)) && continue
                    da, db = PG.dead_trio(A.og, e.a, e.b, r), PG.dead_trio(B.og, e.a, e.b, r)
                    (db && !da) && bump(:com_triBA)
                    (da && !db) && bump(:com_triAB)
                end
            end
            k = dead_ends(A)
            bump(:com_deadA, k)
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:sends, :ps_states, :ps_dead, :ps_dead_states, :com_runs, :com_valid_diff, :com_alive_diff,
            :com_edge_diff, :com_forbid_diff, :com_docs_diff, :com_triBA, :com_triAB, :com_deadA)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDS)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            C[:sends] = length(SENDS)
            foreach(judge, SENDS)
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
