# TrioClique: la vuelta de trío del lado, cubierta por camarillas (29-sept-2026, rama reader-stuck; Lean `StarSide.lean`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_trio_clique.jl <salida.tsv> [muestras] [semilla]
#
# En cada join de e y g, para V la unión fijada en cada color (k_) o una estructura cerrada al azar de la unión (r_),
# y cada cima t de V: F = el lado de t restringido a la estrella S(t) de t en V y revisado (su punto fijo es la vuelta
# de trío de R ∩ lado, probe_join_star_fix.jl). ¿Está toda arista y todo nodo de F en una camarilla llevada de F?
# (todas pasan por t: es la única cima de F). Si sí, esas camarillas dan todos los testigos de TrioSideAt.
#   fe / fv    — aristas / nodos de F         em / vm  — sin camarilla       tr — estrellas truncadas (tope de cadenas)
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

function judge!(V, e, g)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    AV = alive(V)
    for t in collect(get(og.alive, top, SetPathNodesId()))
        L = t in alive(e) ? e : g
        S = Set(z for z in AV if PG.has_edge(og, z, t)); push!(S, t)
        bump(:stars)
        F = restrict(L, intersect(S, alive(L)))
        F.is_valid || (bump(:inval); continue)
        bump(:fe, count(k -> k[1] != k[2], keys(F.og.edges)))
        bump(:fv, length(alive(F)))
        c = GraphPath.edge_clique_miss(F; cap = 20000)
        if c === nothing
            bump(:tr)
        else
            bump(:em, c[1]); bump(:vm, c[2])
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
        append!(cols, Symbol.(pre, ["stars", "inval", "fe", "fv", "em", "vm", "tr"]))
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
