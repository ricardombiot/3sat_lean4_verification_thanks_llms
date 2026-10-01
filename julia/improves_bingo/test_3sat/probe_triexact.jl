# TriExact (30-sept-2026, rama reader-stuck; lean CliqueSound.lean, HClq).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_triexact.jl <salida.tsv>
#
# Con FORBID = :on. ¿Está todo triángulo de un estado en una camarilla de ese estado (un nodo por paso, vecinos dos a
# dos, desde la cima hasta el paso 0)? Se muestrean hasta MAXT triángulos por estado, en las llegadas (:up_done) y en
# las uniones (:join_post), solo tras la fusión central.
#   arr_tri, arr_cl, arr_nocl, arr_forb (triángulos prohibidos), arr_forb_cl (prohibidos y en camarilla)
#   join_tri, join_cl, join_nocl, join_forb, join_forb_cl, unk (presupuesto agotado)
#   *_chain: triángulos en una cadena de la espina; *_forb_chain: prohibidos que están en una cadena de la espina del estado (desde una cima, padres enlazados, vecinos
#   dos a dos): si hay alguno, TriClq tal como se formalizó (sobre OnChain3, sin vida) es falsa.
#   PINS=k (TriClq, CliqueSound.lean): además, en cada estado, k listas de pins al azar (1-3 nodos de mapa por debajo de
#   la cima); se juzga el estado fijado (pin = filter! con revisión) con prefijo parr_/pjoin_. Lanzar siempre con
#   run_capped.sh.

const OUT = abspath(ARGS[1])
const MAXT = parse(Int, get(ENV, "MAXT", "200"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
using Random
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const MACH = Ref{Any}(nothing)
const PINS = parse(Int, get(ENV, "PINS", "0"))

function random_pins(g, n, rng)
    top = Int(g.current_step) - 1
    steps = [s for s in 1:top-1 if length(unique(x.id for x in alive_at(g, s))) >= 2]
    isempty(steps) && return NodeId[]
    [begin ids = unique(x.id for x in alive_at(g, s)); ids[rand(rng, 1:length(ids))] end
     for s in shuffle(rng, steps)[1:min(n, length(steps))]]
end
pin(g, R) = (h = deepcopy(g); h.review_owners = true; GraphPath.filter!(h, SetNodesId(R)); h)

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))

function clique_through(D, must; budget = 20000)
    top = Int(D.current_step) - 1
    mustat = Dict(Int(m.id.step) => m for m in must)
    chosen = PathNodeId[]
    b = Ref(budget)
    function go(k)
        b[] -= 1
        b[] < 0 && return false
        k < 0 && return true
        cands = haskey(mustat, k) ? [mustat[k]] : alive_at(D, k)
        for c in cands
            PG.is_alive(D.og, c) || continue
            all(w -> PG.has_edge(D.og, c, w), chosen) || continue
            all(w -> w == c || PG.has_edge(D.og, c, w), must) || continue
            push!(chosen, c)
            r = go(k - 1)
            pop!(chosen)
            r && return true
            b[] < 0 && return false
        end
        return false
    end
    r = go(top)
    return b[] < 0 ? nothing : r
end

function judge(g, pre, rng)
    g.is_valid || return
    g.map_parent_id === nothing && return
    startswith(SatMachine.map_get_node(MACH[].gmap, g.map_parent_id).title, "or") || return
    judge_state(g, pre, rng)
    for _ in 1:PINS
        R = random_pins(g, rand(rng, 1:3), rng)
        isempty(R) && continue
        h = pin(g, R)
        h.is_valid || continue
        bump(Symbol("p", pre, "_runs"))
        judge_state(h, "p" * pre, rng)
    end
end

# ¿hay una cadena de la espina (desde una cima, padres enlazados, vecinos dos a dos) que pase por los tres nodos?
function chain_through(D, must; budget = 20000)
    top = Int(D.current_step) - 1
    low = minimum(Int(m.id.step) for m in must)
    mustat = Dict(Int(m.id.step) => m for m in must)
    chosen = PathNodeId[]
    b = Ref(budget)
    function go(k, prev)
        b[] -= 1
        b[] < 0 && return false
        k < low && return true
        cands = if prev === nothing
            alive_at(D, k)
        else
            nd = PathCollectionLines.get_node(D.table_lines, prev)
            nd === nothing ? PathNodeId[] : collect(nd.parents)
        end
        haskey(mustat, k) && (cands = [c for c in cands if c == mustat[k]])
        for c in cands
            PG.is_alive(D.og, c) || continue
            all(w -> PG.has_edge(D.og, c, w), chosen) || continue
            push!(chosen, c)
            r = go(k - 1, c)
            pop!(chosen)
            r && return true
            b[] < 0 && return false
        end
        return false
    end
    r = go(top, nothing)
    return b[] < 0 ? nothing : r
end

function judge_state(g, pre, rng)
    xs = [x for (_, s) in g.og.alive for x in s]
    length(xs) < 3 && return
    n = 0
    for _ in 1:(50 * MAXT)
        n >= MAXT && break
        a, b, c = xs[rand(rng, 1:length(xs))], xs[rand(rng, 1:length(xs))], xs[rand(rng, 1:length(xs))]
        (a.id.step != b.id.step && a.id.step != c.id.step && b.id.step != c.id.step) || continue
        (PG.has_edge(g.og, a, b) && PG.has_edge(g.og, a, c) && PG.has_edge(g.og, b, c)) || continue
        n += 1
        bump(Symbol(pre, "_tri"))
        forb = PG.dead_trio(g.og, a, b, c)
        forb && bump(Symbol(pre, "_forb"))
        ch = chain_through(g, [a, b, c])
        if ch === nothing
            bump(:unk)
        elseif ch
            bump(Symbol(pre, "_chain")); forb && bump(Symbol(pre, "_forb_chain"))
        end
        r = clique_through(g, [a, b, c])
        if r === nothing
            bump(:unk)
        elseif r
            bump(Symbol(pre, "_cl"))
            forb && bump(Symbol(pre, "_forb_cl"))
        else
            bump(Symbol(pre, "_nocl"))
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:arr_tri, :arr_cl, :arr_nocl, :arr_forb, :arr_forb_cl, :join_tri, :join_cl, :join_nocl, :join_forb,
            :join_forb_cl, :parr_runs, :parr_tri, :parr_cl, :parr_nocl, :parr_forb, :parr_forb_cl, :pjoin_runs,
            :pjoin_tri, :pjoin_cl, :pjoin_nocl, :pjoin_forb, :pjoin_forb_cl, :arr_chain, :join_chain, :parr_chain, :pjoin_chain, :arr_forb_chain, :join_forb_chain, :parr_forb_chain, :pjoin_forb_chain, :unk)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        rng = MersenneTwister(1)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            MACH[] = machine
            Probes.with(:up_done => g -> judge(g, "arr", rng), :join_post => g -> judge(g, "join", rng)) do
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
