# ¿Las estrellas de un estado son cerradas por la vuelta de trío? (29-sept-2026, rama reader-stuck; StarOneSide)
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_trio_closed.jl <salida.tsv>
#
# EClosed (en un estado h: la llegada e, g o la unión u): para cada cima t de h y su estrella S (vivos que posee t),
# una pareja y–w de nodos de S en pasos distintos que NO es arista de h pero tiene, en todo paso, un testigo común r ∈ S
# (aristas de h) es un «hueco» de h. Columnas por estado (e_, g_, u_): stars, cand (parejas no aristas en S, pasos
# distintos), hole (huecos).

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
const SIDES = Ref{Any}(nothing)

function holes!(h, pre)
    h.is_valid || return
    og = h.og; top = h.current_step - 1
    for t in get(og.alive, top, SetPathNodesId())
        S = [z for z in alive(h) if PG.has_edge(og, z, t)]
        bump(Symbol(pre, "stars"))
        byl = Dict{Int, Vector{PathNodeId}}()
        for r in S
            push!(get!(byl, Int(r.id.step), PathNodeId[]), r)
        end
        for (i, y) in enumerate(S), j in i+1:length(S)
            w = S[j]
            (y.id.step == w.id.step || PG.has_edge(og, y, w)) && continue
            bump(Symbol(pre, "cand"))
            sup = all(0:h.current_step-1) do l
                any(r -> PG.has_edge(og, y, r) && PG.has_edge(og, w, r), get(byl, l, PathNodeId[]))
            end
            sup && bump(Symbol(pre, "hole"))
        end
    end
end

function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    u.current_step >= 2 || return
    holes!(e, "e_"); holes!(g, "g_"); holes!(u, "u_")
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = Symbol[]
    for pre in ("e_", "g_", "u_"), c in ("stars", "cand", "hole")
        push!(cols, Symbol(pre, c))
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
