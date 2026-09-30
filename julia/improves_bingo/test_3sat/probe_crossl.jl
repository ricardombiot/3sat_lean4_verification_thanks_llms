# CrossClosedL (30-sept-2026, rama reader-stuck; lean LiveJoin.lean CrossClosedL, LiveLine.lean PinCrossL).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf test_3sat/run_capped.sh 4000 900 julia --heap-size-hint=3G --project=. \
#       test_3sat/probe_crossl.jl <salida.tsv> [muestras]
#
# Siempre con tope de memoria (run_capped.sh). Sin pins se usan la unión de la máquina y los lados de :join_pre (copiar
# y volver a unir los lados sin pins satura la memoria). NOWEAK=1 / NOSTRONG=1 saltan cada medida.
#
# Con FORBID = :on. En cada join (:join_pre / :join_post), para R = [] y para `muestras` listas de pins al azar (1-3
# nodos de mapa por debajo de la cima): A' = pin(A,R), B' = pin(B,R); si los dos son válidos, U = join(A',B'). Se
# recorren las cadenas vivas de U desde cada cima (padres vivos, vecinos dos a dos, sin trío prohibido en U). Con S el
# lado de la cima (viva solo en él) y O el otro, si la cadena es cadena de S (nodos, aristas y enlaces en S), cada trío
# nuevo prohibido en S debe estar cortado en O (le falta una arista o O lo prohíbe): eso es CrossClosedL.
#   runs, pin_runs, chains, notside (cadena de U que no es cadena de S), forb (tríos prohibidos en S en cadenas de S),
#   viol (de ellos, abiertos en O: CrossClosedL falla), viol_pin (con R no vacía),
#   strong, strong_viol (CrossClosed fuerte en todas las cadenas de S, sin mirar U, con pins), cap

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 3
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20260930))
const PRE = Ref{Any}(nothing)
const STAGE = Ref(:none)

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b ? PG.is_alive(g.og, a) : PG.has_edge(g.og, a, b)
dead(g, a, b, r) = length(unique((a, b, r))) == 3 && PG.has_edge(g.og, a, b) && PG.dead_trio(g.og, a, b, r)
tri(g, a, b, x) = PG.has_edge(g.og, a, b) && PG.has_edge(g.og, a, x) && PG.has_edge(g.og, b, x)
cut(o, a, b, x) = !tri(o, a, b, x) || PG.dead_trio(o.og, a, b, x)

function random_pins(g, n)
    top = Int(g.current_step) - 1
    steps = [s for s in 1:top-1 if length(unique(x.id for x in alive_at(g, s))) >= 2]
    isempty(steps) && return NodeId[]
    [begin ids = unique(x.id for x in alive_at(g, s)); ids[rand(RNG[], 1:length(ids))] end
     for s in shuffle(RNG[], steps)[1:min(n, length(steps))]]
end
pin(g, R) = (h = deepcopy(g); h.review_owners = true; GraphPath.filter!(h, SetNodesId(R)); h)

function live_parents(g, x, chain)
    nd = PathCollectionLines.get_node(g.table_lines, x)
    nd === nothing && return PathNodeId[]
    [p for p in nd.parents if PG.is_alive(g.og, p) && all(w -> adj(g, w, p), chain) &&
        !any(dead(g, chain[i], chain[j], p) for i in eachindex(chain) for j in i+1:length(chain))]
end

# ¿sigue siendo cadena de s al añadir chain[end]?
function in_side(s, chain)
    x = chain[end]
    PG.is_alive(s.og, x) || return false
    all(w -> adj(s, w, x), chain) || return false
    if length(chain) >= 2
        nd = PathCollectionLines.get_node(s.table_lines, chain[end-1])
        (nd === nothing || !(x in nd.parents)) && return false
    end
    true
end

function weak_dfs(U, x, s, o, ok, chain, leaves, pinned)
    leaves[] > CAP && return
    push!(chain, x)
    bump(:chains)
    ok = ok && in_side(s, chain)
    ok || bump(:notside)
    if ok
        k = length(chain)
        for i in 1:k-1, j in i+1:k-1
            a, b = chain[i], chain[j]
            PG.dead_trio(s.og, a, b, x) || continue
            bump(:forb)
            if !cut(o, a, b, x)
                bump(:viol); pinned && bump(:viol_pin)
            end
        end
    end
    if Int(x.id.step) == 0
        leaves[] += 1
    else
        for p in live_parents(U, x, chain)
            weak_dfs(U, p, s, o, ok, chain, leaves, pinned)
        end
    end
    pop!(chain)
    nothing
end

function weak(U, pa, pb, pinned)
    top = Int(U.current_step) - 1
    leaves = Ref(0)
    for t in alive_at(U, top)
        ia, ib = PG.is_alive(pa.og, t), PG.is_alive(pb.og, t)
        ia == ib && continue
        s, o = ia ? (pa, pb) : (pb, pa)
        weak_dfs(U, t, s, o, true, PathNodeId[], leaves, pinned)
    end
    leaves[] > CAP && bump(:cap)
end

# CrossClosed fuerte: todas las cadenas de s
function strong_dfs(s, o, x, chain, leaves)
    leaves[] > CAP && return
    push!(chain, x)
    k = length(chain)
    for i in 1:k-1, j in i+1:k-1
        a, b = chain[i], chain[j]
        PG.dead_trio(s.og, a, b, x) || continue
        bump(:strong)
        cut(o, a, b, x) || bump(:strong_viol)
    end
    if Int(x.id.step) > 0
        nd = PathCollectionLines.get_node(s.table_lines, x)
        if nd !== nothing
            for p in nd.parents
                PG.is_alive(s.og, p) && all(w -> adj(s, w, p), chain) && strong_dfs(s, o, p, chain, leaves)
            end
        end
    else
        leaves[] += 1
    end
    pop!(chain)
    nothing
end

function strong(s, o)
    leaves = Ref(0)
    for t in alive_at(s, Int(s.current_step) - 1)
        strong_dfs(s, o, t, PathNodeId[], leaves)
    end
end

function judge(u, a, b)
    u.is_valid || return
    Rs = [NodeId[]]
    for _ in 1:SAMPLES
        R = random_pins(u, rand(RNG[], 1:3))
        isempty(R) || push!(Rs, R)
    end
    for R in Rs
        # sin pins: la unión es la de la máquina (u) y los lados son los de :join_pre
        if isempty(R)
            pa, pb, U = a, b, u
        else
            STAGE[] = :pin
            pa, pb = pin(a, R), pin(b, R)
            (pa.is_valid && pb.is_valid) || continue
            STAGE[] = :join
            U = deepcopy(pa); GraphPath.do_join!(U, pb)
            U.is_valid || continue
        end
        bump(:runs); isempty(R) || bump(:pin_runs)
        get(ENV, "NOWEAK", "0") == "1" || (STAGE[] = :weak; weak(U, pa, pb, !isempty(R)))
        get(ENV, "NOSTRONG", "0") == "1" || (STAGE[] = :strong; strong(pa, pb); strong(pb, pa))
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:runs, :pin_runs, :chains, :notside, :forb, :viol, :viol_pin, :strong, :strong_viol, :cap)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            Probes.with(:join_pre => (a, b) -> (PRE[] = (deepcopy(a), deepcopy(b))),
                        :join_post => u -> (PRE[] === nothing || try judge(deepcopy(u), PRE[]...) catch e
                            get(C, :err, 0) == 0 && Core.println("ERR ", typeof(e), " stage=", STAGE[]); bump(:err)
                        end; PRE[] = nothing)) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
