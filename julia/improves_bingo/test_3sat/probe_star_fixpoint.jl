# El punto fijo del review dentro de la estrella de una cima (29-sept-2026, rama reader-stuck; Lean `StarNodes.lean`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_star_fixpoint.jl <salida.tsv> [muestras] [semilla]
#
# En cada join de e y g, para V la unión fijada en cada color c (prefijo k_) o una estructura cerrada al azar de la
# unión (restringir y revisar; prefijo r_, `muestras` por join), y cada cima t de V: S(t) = vivos de V que posee t.
# Se restringe V a S(t) y se revisa (el punto fijo, F). Se compara el conjunto de aristas de F con candidatos
# explícitos, todos dentro de S(t):
#   all   — todas las aristas de V entre nodos de S(t)
#   tri   — las que forman triángulo con t (x–t y w–t en V)
#   side  — las que además son aristas del lado de t (e si t vive en e, g si no)
#   trio1 — una vuelta de la regla de trío: en cada paso un testigo r en S(t) con x–r, w–r en V
# Columnas: stars; nodos que F pierde (nf); aristas de F; y para cada candidato, estrellas con igualdad exacta (_eq),
# aristas de F fuera del candidato (_miss) y aristas del candidato fuera de F (_extra).

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

function compare!(tag, cand, EF)
    bump(Symbol(tag, "_eq"), cand == EF ? 1 : 0)
    bump(Symbol(tag, "_miss"), length(setdiff(EF, cand)))
    bump(Symbol(tag, "_extra"), length(setdiff(cand, EF)))
end

function judge!(V, e, g)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    for t in collect(get(og.alive, top, SetPathNodesId()))
        S = Set(z for z in alive(V) if PG.has_edge(og, z, t)); push!(S, t)
        side = t in alive(e) ? e : g
        F = restrict(V, S)
        bump(:stars)
        AF = F.is_valid ? alive(F) : Set{PathNodeId}()
        bump(:nf, length(setdiff(S, AF)))
        EF = F.is_valid ? edges(F) : Set{Tuple{PathNodeId,PathNodeId}}()
        bump(:ef, length(EF))
        all_ = Set((y, w) for (y, w) in edges(V) if y in S && w in S)
        tri = Set((y, w) for (y, w) in all_ if PG.has_edge(og, y, t) && PG.has_edge(og, w, t))
        sd = Set((y, w) for (y, w) in tri if PG.has_edge(side.og, y, w))
        trio1 = Set((y, w) for (y, w) in tri if all(0:V.current_step-1) do l
            any(r -> r in S && PG.has_edge(og, y, r) && PG.has_edge(og, w, r), get(og.alive, l, SetPathNodesId()))
        end)
        compare!("all", all_, EF); compare!("tri", tri, EF); compare!("side", sd, EF); compare!("trio1", trio1, EF)
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
        append!(cols, Symbol.(pre, ["stars", "nf", "ef"]))
        for c in ("all", "tri", "side", "trio1"), s in ("_eq", "_miss", "_extra")
            push!(cols, Symbol(pre, c, s))
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
