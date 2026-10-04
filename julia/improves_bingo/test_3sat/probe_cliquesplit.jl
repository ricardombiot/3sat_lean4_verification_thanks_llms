# CliqueSplit (29-sept-2026, rama reader-stuck): toda camarilla llevada por la unión es camarilla de un lado.
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_cliquesplit.jl <salida.tsv> [tope]
#
# En cada join se enumeran las camarillas de la unión (cadenas de enlaces raíz → cima, vivas, poseídas dos a dos,
# hasta `tope`) y se mira si todas sus parejas son posesiones de e (y sus nodos vivos en e), o de g.
# Por instancia: joins, cliques, split_f (camarillas que no son de ningún lado), trunc (joins que se pasan del tope).

const OUT = abspath(ARGS[1])
const CAP = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const PCL = PathCollectionLines
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const SIDES = Ref{Any}(nothing)

carried_in(h, chain) = all(x -> PG.is_alive(h.og, x), chain) &&
    all(PG.has_edge(h.og, chain[i], chain[j]) for i in eachindex(chain) for j in i+1:length(chain))

function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    bump(:joins)
    og = u.og; top = u.current_step - 1
    chain = PathNodeId[]; n = Ref(0); over = Ref(false)
    function ext(x)
        over[] && return
        push!(chain, x)
        if x.id.step == top
            n[] += 1
            n[] > CAP && (over[] = true)
            bump(:cliques)
            (carried_in(e, chain) || carried_in(g, chain)) || bump(:split_f)
        else
            nd = PCL.get_node(u.table_lines, x)
            if nd !== nothing
                for s in nd.sons
                    PG.is_alive(og, s) || continue
                    PCL.get_node(u.table_lines, s) === nothing && continue
                    all(a -> PG.has_edge(og, a, s), chain) && ext(s)
                end
            end
        end
        pop!(chain)
    end
    for r in get(og.alive, 0, SetPathNodesId())
        r.parent_id === nothing || continue
        PCL.get_node(u.table_lines, r) === nothing && continue
        ext(r)
    end
    over[] && bump(:trunc)
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :cliques, :split_f, :trunc)
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
