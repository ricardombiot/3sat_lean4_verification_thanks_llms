# ArrivalGap (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_arrival_gap.jl <salida.tsv>
#
# Para cada llegada X (UP de un remitente S hacia un destino) y cada pareja y–w que es arista de S, con y, w vivos en
# X y que X ya no tiene (la quitó la llegada): ¿hay un paso l (no el de y ni el de w) en el que ningún vivo r de X en
# el paso l posee a y y a w por aristas de TODAS las llegadas de ese paso (de cualquier remitente a cualquier destino)?
#   arrivals, np (parejas quitadas), nf (sin tal paso: falla), nf_self (sin paso libre ni siquiera con las aristas de X:
#   no debería pasar, la regla de parejas deja un hueco); g1: hay paso libre con las aristas del remitente S (sobre los
#   vivos de X); g2_bad: alguna arista de otra llegada entre y (o w) y un vivo de X no es del remitente; g1E: paso libre
#   con aristas del remitente o de cualquier llegada

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const ARR = Any[]          # (paso, remitente, llegada)
const CUR = Ref{Any}(nothing)

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        $(CUR)[] = deepcopy(gpath)
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        gpath.is_valid && push!($(ARR), (Int(gpath.current_step), $(CUR)[], deepcopy(gpath)))
    end
end)

alive(h) = [x for (_, xs) in h.og.alive for x in xs]

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:arrivals, :np, :nf, :nf_self, :g1, :g2_bad, :g1E)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(ARR)
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            bystep = Dict{Int, Vector{Any}}()
            for (st, S, X) in ARR
                push!(get!(bystep, st, Any[]), (S, X))
            end
            for (st, xs) in bystep
                ogs = [X.og for (_, X) in xs]
                E(a, b) = any(o -> PG.has_edge(o, a, b), ogs)
                for (S, X) in xs
                    bump(:arrivals)
                    AX = alive(X); SX = Set(AX)
                    byl = Dict{Int, Vector{PathNodeId}}()
                    for r in AX
                        push!(get!(byl, Int(r.id.step), PathNodeId[]), r)
                    end
                    for (y, w) in keys(S.og.edges)
                        (y == w || !(y in SX) || !(w in SX) || PG.has_edge(X.og, y, w)) && continue
                        bump(:np)
                        ends = (Int(y.id.step), Int(w.id.step))
                        free(adj) = any(0:st-1) do l
                            (l in ends) && return false
                            all(r -> !(adj(y, r) && adj(w, r)), get(byl, l, PathNodeId[]))
                        end
                        free((a, b) -> PG.has_edge(X.og, a, b)) || bump(:nf_self)
                        free(E) || bump(:nf)
                        # G1: el hueco con las aristas del remitente, sobre los vivos de X
                        free((a, b) -> PG.has_edge(S.og, a, b)) && bump(:g1)
                        # G2: aristas de otras llegadas entre y (o w) y vivos de X que no son del remitente
                        g2bad = any(AX) do r
                            any(((y, r), (w, r))) do (a, b)
                                a != b && !PG.has_edge(S.og, a, b) && any(o -> o !== X.og && PG.has_edge(o, a, b), ogs)
                            end
                        end
                        g2bad && bump(:g2_bad)
                        # G1 con aristas del remitente o de otras llegadas
                        free((a, b) -> PG.has_edge(S.og, a, b) || E(a, b)) && bump(:g1E)
                    end
                end
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
