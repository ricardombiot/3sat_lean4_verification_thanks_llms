# ChainOpen (30-sept-2026, rama reader-stuck): ¿contiene alguna cadena un trío prohibido?
#
#   ABL=none|noup PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_chainopen.jl <salida.tsv>
#
# Con FORBID = :on. Una cadena: de una cima hacia abajo por padres vivos, vecinos dos a dos (SIN mirar tríos). Se
# recorren todas (hasta CAP hojas por estado) y se cuenta cuántas contienen un trío prohibido del estado.
#   arr_*  — llegadas (:up_done);  join_* — uniones recién hechas (:join_post)
#   *_nodes (nodos de cadena recorridos), *_bad (nodos donde la cadena pasa a tener un trío prohibido),
#   *_bad_top (de ellos, con el trío prohibido que contiene la cima)

const OUT = abspath(ARGS[1])
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)

const ABL = get(ENV, "ABL", "none")
if ABL in ("noup", "noboth")
    Core.eval(PathOwnersGraph, :(up_forbid!(g :: OwnersGraph, n :: PathNodeId, parents) = nothing))
end

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
adj(g, a, b) = a == b ? PG.is_alive(g.og, a) : PG.has_edge(g.og, a, b)

function judge(g, pre)
    g.is_valid || return
    bump(Symbol(pre, "_states"))
    top = Int(g.current_step) - 1
    leaves = Ref(0)
    chain = PathNodeId[]
    function dfs(x, bad)
        leaves[] > CAP && return
        push!(chain, x)
        bump(Symbol(pre, "_nodes"))
        k = length(chain)
        newbad = false; newtop = false
        if !bad
            for i in 1:k-1, j in i+1:k-1
                if PG.dead_trio(g.og, chain[i], chain[j], x)
                    newbad = true; i == 1 && (newtop = true)
                end
            end
            newbad && bump(Symbol(pre, "_bad"))
            newtop && bump(Symbol(pre, "_bad_top"))
        end
        if Int(x.id.step) == 0
            leaves[] += 1
        else
            nd = PathCollectionLines.get_node(g.table_lines, x)
            if nd !== nothing
                for p in nd.parents
                    PG.is_alive(g.og, p) && all(w -> adj(g, w, p), chain) && dfs(p, bad || newbad)
                end
            end
        end
        pop!(chain)
    end
    for t in alive_at(g, top)
        dfs(t, false)
    end
    leaves[] > CAP && bump(Symbol(pre, "_cap"))
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:arr_states, :arr_nodes, :arr_bad, :arr_bad_top, :arr_cap, :join_states, :join_nodes, :join_bad,
            :join_bad_top, :join_cap)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            Probes.with(:up_done => g -> judge(g, "arr"), :join_post => g -> judge(g, "join")) do
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
