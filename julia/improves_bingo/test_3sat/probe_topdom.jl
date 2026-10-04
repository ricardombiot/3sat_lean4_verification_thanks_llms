# TopDom (30-sept-2026, rama reader-stuck; tras probe_joinside).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_topdom.jl <salida.tsv>
#
# Con FORBID = :on. TopDom(g): para todo trío prohibido (a,b,c) y toda cima t vecina de los tres, algún trío
# (t,x,y) con {x,y} ⊂ {a,b,c} está cortado en g (falta una de sus aristas o está prohibido).
# Se mide en las llegadas (:up_done) y en las uniones (:join_post). Además, en las llegadas, para cada cima con dos
# padres vecinos de (a,b,c): ¿los dos padres tienen una pareja cortada en común? (split: no la tienen).
#   *_trios (tríos prohibidos con alguna cima vecina de los tres), *_viol (cima sin trío cortado),
#   arr_two (casos con dos padres vecinos), arr_split (sin pareja común en el remitente)

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
cut(g, t, x, y) = !(PG.has_edge(g.og, t, x) && PG.has_edge(g.og, t, y) && PG.has_edge(g.og, x, y)) ||
                  PG.dead_trio(g.og, t, x, y)
pairs(tri) = ((tri[1], tri[2]), (tri[1], tri[3]), (tri[2], tri[3]))

function forbidden_trios(g)
    out = NTuple{3, PathNodeId}[]
    for (k, e) in g.og.edges, r in e.forbid
        PG.node_ord(k[2]) < PG.node_ord(r) || continue
        (PG.is_alive(g.og, r) && PG.has_edge(g.og, k[1], r) && PG.has_edge(g.og, k[2], r)) || continue
        push!(out, (k[1], k[2], r))
    end
    return out
end

function judge(g, pre)
    g.is_valid || return
    top = Int(g.current_step) - 1
    tops = alive_at(g, top)
    for tri in forbidden_trios(g)
        any(x -> Int(x.id.step) >= top, tri) && continue
        adjt = [t for t in tops if all(x -> PG.has_edge(g.og, t, x), tri)]
        isempty(adjt) && continue
        bump(Symbol(pre, "_trios"))
        for t in adjt
            any(p -> cut(g, t, p...), pairs(tri)) || bump(Symbol(pre, "_viol"))
            if pre == "arr"
                nd = PathCollectionLines.get_node(g.table_lines, t)
                nd === nothing && continue
                ps = [p for p in nd.parents if PG.is_alive(g.og, p) && all(x -> PG.has_edge(g.og, p, x), tri)]
                length(ps) >= 2 || continue
                bump(:arr_two)
                common = [pr for pr in pairs(tri) if all(p -> cut(g, p, pr...), ps)]
                isempty(common) && bump(:arr_split)
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:arr_trios, :arr_viol, :arr_two, :arr_split, :join_trios, :join_viol)
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
