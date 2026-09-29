# StarJoinDown: qué es el punto fijo del lado en la estrella (29-sept-2026, rama reader-stuck; Lean `StarLine.lean`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_join_star_fix.jl <salida.tsv> [muestras] [semilla]
#
# Como probe_join_down.jl, pero se compara el conjunto de aristas del punto fijo F (el lado L de la cima restringido
# a la estrella S(t) de t en V, revisado) con candidatos explícitos entre nodos de S(t):
#   eall  — aristas de L                         ev    — aristas de L que también son de V
#   tl    — una vuelta de trío en L (testigo común en S(t) por aristas de L)
#   tlv   — una vuelta de trío en L ∩ V (aristas y testigos por aristas de L y de V)
# _eq estrellas con igualdad, _miss aristas de F fuera, _extra aristas del candidato fuera de F.
#
# En cada join de e y g, para V la unión fijada en cada color (k_) o una estructura cerrada al azar de la unión (r_),
# y cada cima t de V: t vive en un lado (L = e o g). Se restringe L a los nodos de V (y, aparte, a los de la estrella
# S(t) de t en V) y se revisa. Para cada z de S(t):
#   zv_f — z no sobrevive en L restringido a V (JoinDown falla)
#   zs_f — z no sobrevive en L restringido a S(t) (versión fuerte: la estrella dentro del lado)
#   both — t en los dos lados (no debería pasar: TopsApart)
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
        ine = t in alive(e); ing = t in alive(g)
        ine && ing && bump(:both)
        L = ine ? e : g
        S = Set(z for z in AV if PG.has_edge(og, z, t)); push!(S, t)
        bump(:stars)
        hv = restrict(L, intersect(AV, alive(L)))
        hs = restrict(L, intersect(S, alive(L)))
        Av = hv.is_valid ? alive(hv) : Set{PathNodeId}()
        As = hs.is_valid ? alive(hs) : Set{PathNodeId}()
        for z in S
            bump(:z)
            z in Av || bump(:zv_f)
            z in As || bump(:zs_f)
        end
        EF = hs.is_valid ? edges(hs) : Set{Tuple{PathNodeId,PathNodeId}}()
        lo = L.og
        both(y, w) = PG.has_edge(lo, y, w) && PG.has_edge(og, y, w)
        E(p) = Set((y, w) for (y, w) in keys(lo.edges) if y != w && y in S && w in S && p(y, w))
        eall = E((y, w) -> true)
        ev = E(both)
        wit(q) = (y, w) -> all(0:V.current_step-1) do l
            any(r -> r in S && q(y, r) && q(w, r), get(lo.alive, l, SetPathNodesId()))
        end
        tl = E(wit((a, b) -> PG.has_edge(lo, a, b)))
        tlv = E((y, w) -> both(y, w) && wit(both)(y, w))
        for (nm, c) in (("eall", eall), ("ev", ev), ("tl", tl), ("tlv", tlv))
            bump(Symbol(nm, "_eq"), c == EF ? 1 : 0)
            bump(Symbol(nm, "_miss"), length(setdiff(EF, c)))
            bump(Symbol(nm, "_extra"), length(setdiff(c, EF)))
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
        append!(cols, Symbol.(pre, ["stars", "both", "z", "zv_f", "zs_f"]))
        for c in ("eall", "ev", "tl", "tlv"), x in ("_eq", "_miss", "_extra")
            push!(cols, Symbol(pre, c, x))
        end
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
