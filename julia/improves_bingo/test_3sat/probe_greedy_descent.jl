# Bajada sin retroceso (29-sept-2026, rama reader-stuck; Lean `StarUnion.lean`, `UnionTopClique`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_greedy_descent.jl <salida.tsv> [muestras] [semilla]
#
# En cada join, para V la unión fijada en cada color (k_) o una estructura cerrada al azar de la unión (r_), cada cima
# t de V y cada z ≠ t de su estrella: se baja desde t por padres (documentos de V), eligiendo en cada paso un padre del
# último nodo, vivo en V, que posea (en V) a todos los ya elegidos y a z (en el paso de z, el propio z), hasta una raíz.
#   pairs  — parejas (t, z)
#   none   — ninguna cadena completa (UnionTopClique falla dentro de V)
#   dead   — cadenas parciales sin continuación (callejones: la bajada tendría que retroceder)
#   pdead  — parejas con algún callejón        greedy — parejas donde la bajada «primer candidato» se atasca
#   tr     — parejas truncadas (tope de nodos de la búsqueda)
# Con prefijo f: lo mismo dentro de F, el punto fijo de V restringida a la estrella de t (la vuelta de trío);
# fmiss — z no está en F.
using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 4
const RNG = Ref(MersenneTwister(length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
const PRE = Ref("k_")
bump(k, n = 1) = (k = Symbol(PRE[], k); C[k] = get(C, k, 0) + n)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
edges(h) = Set((y, w) for (y, w) in keys(h.og.edges) if y != w)
function restrict(g, U)
    h = deepcopy(g)
    for x in collect(alive(h))
        x in U && continue
        GraphPath.remove_node_owner!(h, x; rule = :probe)
    end
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end
pin(g, P) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(P)); g2)

const CAP = 20000
parents_of(V, x) = (n = PathCollectionLines.get_node(V.table_lines, x); n === nothing ? PathNodeId[] : collect(n.parents))

function descend(V, t, z)
    og = V.og
    ok(c, chain) = PG.is_alive(og, c) && all(a -> PG.has_edge(og, a, c), chain) &&
        (c.id.step > z.id.step ? PG.has_edge(og, c, z) : (c.id.step == z.id.step ? c == z : true))
    cands(chain) = [c for c in parents_of(V, last(chain)) if ok(c, chain)]
    complete(chain) = last(chain).id.step == 0 && last(chain).parent_id === nothing
    visits = Ref(0); dead = Ref(0); found = Ref(false); over = Ref(false)
    function dfs(chain)
        over[] && return
        visits[] += 1; visits[] > CAP && (over[] = true; return)
        if complete(chain); found[] = true; return; end
        cs = cands(chain)
        isempty(cs) && (dead[] += 1; return)
        for c in cs
            push!(chain, c); dfs(chain); pop!(chain)
        end
    end
    dfs([t])
    # la bajada «primer candidato»
    chain = [t]; gstuck = false
    while !complete(chain)
        cs = cands(chain)
        isempty(cs) && (gstuck = true; break)
        push!(chain, first(sort(cs, by = string)))
    end
    return (found[], dead[], gstuck, over[])
end

# Bajada con fijación y review, como el lector: se fija el paso de t en t y el de z en z (se quitan los demás vivos de
# esos pasos) y se revisa; después, en cada paso, para cada padre candidato c del último nodo, se fija su paso en c y
# se revisa: rv_bad cuenta los candidatos tras cuyo review ya no están vivos la cadena y z; se sigue por el primero bueno.
#   rv_pairs / rv_pin0 (el review de t y z ya mata algo) / rv_bad / rv_stuck (ningún candidato bueno)
function pin_step(H, c)
    keep = Set(x for x in alive(H) if x.id.step != c.id.step || x == c)
    return restrict(H, keep)
end

function descend_review(V, t, z)
    H = pin_step(pin_step(V, t), z)
    chain = [t]
    ok0 = H.is_valid && t in alive(H) && z in alive(H)
    ok0 || return (false, 0, false)
    bad = 0
    while !(last(chain).id.step == 0 && last(chain).parent_id === nothing)
        og = H.og
        cs = [c for c in parents_of(H, last(chain)) if PG.is_alive(og, c) && all(a -> PG.has_edge(og, a, c), chain) &&
              (c.id.step > z.id.step ? PG.has_edge(og, c, z) : (c.id.step == z.id.step ? c == z : true))]
        next = nothing
        for c in sort(cs, by = string)
            H2 = pin_step(H, c)
            if H2.is_valid && all(a -> a in alive(H2), chain) && c in alive(H2) && z in alive(H2)
                next === nothing && (next = (c, H2))
            else
                bad += 1
            end
        end
        next === nothing && return (true, bad, true)
        push!(chain, next[1]); H = next[2]
    end
    return (true, bad, false)
end

function judge!(V, e, g)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    AV = alive(V)
    for t in collect(get(og.alive, top, SetPathNodesId()))
        S = Set(z for z in AV if PG.has_edge(og, z, t)); push!(S, t)
        F = restrict(V, S)      # el punto fijo de la estrella (la vuelta de trío)
        for z in AV
            (z == t || !PG.has_edge(og, z, t)) && continue
            bump(:pairs)
            f, d, gs, ov = descend(V, t, z)
            ov && (bump(:tr); continue)
            f || bump(:none)
            bump(:dead, d); d > 0 && bump(:pdead)
            gs && bump(:greedy)
            if PRE[] == "k_"
                bump(:rv_pairs)
                ok0, bad, stuck = descend_review(V, t, z)
                ok0 || bump(:rv_pin0)
                bump(:rv_bad, bad); stuck && bump(:rv_stuck)
            end
            # dentro de F
            if F.is_valid && z in alive(F)
                f2, d2, gs2, ov2 = descend(F, t, z)
                ov2 && continue
                f2 || bump(:fnone)
                bump(:fdead, d2); d2 > 0 && bump(:fpdead)
                gs2 && bump(:fgreedy)
            else
                bump(:fmiss)
            end
        end
    end
end

const SIDES = Ref{Any}(nothing)
function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    k = u.current_step - 2
    k >= 0 || return
    for c in unique(x.id for x in get(u.og.alive, k, SetPathNodesId()))
        PRE[] = "k_"; judge!(pin(u, [c]), e, g)
    end
    for _ in 1:SAMPLES
        p = rand(RNG[], (0.5, 0.7, 0.9))
        PRE[] = "r_"; judge!(restrict(u, Set(x for x in alive(u) if rand(RNG[]) < p)), e, g)
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = Symbol[]
    for pre in ("r_", "k_")
        append!(cols, Symbol.(pre, ["pairs", "none", "dead", "pdead", "greedy", "tr", "fmiss", "fnone", "fdead", "fpdead", "fgreedy", "rv_pairs", "rv_pin0", "rv_bad", "rv_stuck"]))
    end
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b))),
                                 :join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
