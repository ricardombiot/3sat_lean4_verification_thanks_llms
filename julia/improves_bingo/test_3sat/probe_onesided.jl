# OneSideSupport (29-sept-2026, rama reader-stuck): una pareja de la unión entre nodos de e que es de g y no de e
# tiene un paso l en el que todos sus testigos comunes en la unión están fuera de e (y al revés con g).
# Si vale, SideEdgesAt sale directo: una estructura de la unión fijada en el color de e solo tiene nodos de e.
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_onesided.jl <salida.tsv>

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

function check!(u, A, B, tag_t, tag_f)
    Aal = alive(A)
    for (y, w) in keys(B.og.edges)
        (y == w || !(y in Aal) || !(w in Aal) || PG.has_edge(A.og, y, w)) && continue
        bump(tag_t)
        ok = any(0:u.current_step-1) do l
            all(r -> !(r in Aal), (r for r in get(u.og.alive, l, SetPathNodesId())
                                   if PG.has_edge(u.og, y, r) && PG.has_edge(u.og, w, r)))
        end
        ok || bump(tag_f)
    end
end

function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    bump(:joins)
    check!(u, e, g, :ge_t, :ge_f)
    check!(u, g, e, :eg_t, :eg_f)
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :ge_t, :ge_f, :eg_t, :eg_f)
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
