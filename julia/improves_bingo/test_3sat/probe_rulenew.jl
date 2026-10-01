# Los triángulos viejos que prohíbe la regla en una llegada, y qué les pasa después (1-oct-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=v6_c26_i1.cnf julia --project=. test_3sat/probe_rulenew.jl <salida.tsv>
#
# Con FORBID = :on. Para cada llegada válida S = arrOn a d (a en la línea T) y cada triángulo viejo B prohibido en S
# que en `a` es un triángulo sin prohibir (lo prohíbe la regla del review; probe_norule.jl):
#
#   news       cuántos
#   sigS       las cimas de S vecinas de algún par de B, cara a cara (12, 13, 23): o sostiene, D prohibida, - falta arista
#   sigA       lo mismo con las cimas de `a`
#   shapeA     `a` es una llegada sola o una unión, y cómo tiene B cada entrada de la línea T-1
#   next       la entrada de clave d de la línea T+1: «none» (no envía), o cómo tiene B (dead/open/edge/node)
#   after      para cada llegada válida S2 de esa entrada: cómo tiene B, y la mejor cima de S2 sobre B (nostar, f0…f3);
#              «dead:f3» sería una base de PrevCut con la entrada `a` de la línea anterior SIN cortarla
#   broke      en esas llegadas, qué se rompe de B: nodo i muerto (por el filtro directamente o por cascada), arista
#              ij que falta entre vivos, cuántas cimas de S con alguna cara siguen vivas, y los pasos de los requisitos
#              y de los nodos de B relativos a T

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{String, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const SENDS = Any[]

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.is_valid && push!($(SENDS), (deepcopy(gpath), copy(requires), map_id_node, title, prohibited))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
edge(g, a, b) = PG.has_edge(g.og, a, b)
st(x) = Int(x.id.step)
tri(g, b) = edge(g, b[1], b[2]) && edge(g, b[1], b[3]) && edge(g, b[2], b[3])
how(g, b) = !all(n -> PG.is_alive(g.og, n), b) ? "node" : !tri(g, b) ? "edge" :
            PG.dead_trio(g.og, b[1], b[2], b[3]) ? "dead" : "open"
const FACES = ((1, 2), (1, 3), (2, 3))
face(g, p, u, w) = !(edge(g, p, u) && edge(g, p, w)) ? '-' : PG.dead_trio(g.og, p, u, w) ? 'D' : 'o'
sig(g, p, b) = String([face(g, p, b[f[1]], b[f[2]]) for f in FACES])
sigs(g, b) = join(sort(filter(x -> x != "---", [sig(g, p, b) for p in alive_at(g, Int(g.current_step) - 1)])), "/")

function dead_tris(g)
    out = NTuple{3, PathNodeId}[]
    for (k, e) in g.og.edges, r in collect(e.forbid)
        (edge(g, e.a, r) && edge(g, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        push!(out, (e.a, e.b, r))
    end
    return out
end

function cat(g, b)
    best = -1
    for t in alive_at(g, Int(g.current_step) - 1)
        all(x -> edge(g, t, x), b) || continue
        k = count(!, (PG.dead_trio(g.og, t, b[1], b[2]), PG.dead_trio(g.og, t, b[1], b[3]), PG.dead_trio(g.og, t, b[2], b[3])))
        best = max(best, k)
    end
    return best < 0 ? "nostar" : "f$best"
end

function arrival(send)
    (g0, reqs, d, title, proh) = send
    A = deepcopy(g0)
    GraphPath.filter!(A, reqs)
    A.is_valid && GraphPath.do_up!(A, d, title, proh)
    return A
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    header = "instance\ttruth\tnews\tsigS\tsigA\tshapeA\tnext\tafter\tbroke\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDS)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            lines = Dict{Int, Dict{Any, Any}}()
            from = Dict{Any, Vector{Any}}()
            into = Dict{Any, Vector{Any}}()
            for s in SENDS
                L = Int(s[1].current_step)
                get!(get!(lines, L, Dict{Any, Any}()), s[1].map_parent_id, s[1])
                push!(get!(from, (L, s[1].map_parent_id), Any[]), s)
                push!(get!(into, (L, s[3]), Any[]), s)
            end
            for s in SENDS
                a = s[1]
                T = Int(a.current_step)
                S = arrival(s)
                S.is_valid || continue
                for b in dead_tris(S)
                    maximum(st, b) < T || continue
                    (tri(a, b) && PG.dead_trio(a.og, b[1], b[2], b[3])) && continue
                    bump("news")
                    bump("sigS:" * sigs(S, b))
                    bump("sigA:" * sigs(a, b))
                    nin = count(s2 -> arrival(s2).is_valid, get(into, (T - 1, a.map_parent_id), Any[]))
                    bump("shapeA:" * (nin == 2 ? "join" : "single") * ":" *
                         join(sort([how(e, b) for e in values(get(lines, T - 1, Dict{Any, Any}()))]), "+"))
                    nxt = get(get(lines, T + 1, Dict{Any, Any}()), s[3], nothing)
                    if nxt === nothing
                        bump("next:none"); continue
                    end
                    bump("next:" * how(nxt, b))
                    for s2 in get(from, (T + 1, s[3]), Any[])
                        S2 = arrival(s2)
                        if !S2.is_valid
                            bump("after:invalid"); continue
                        end
                        h2 = how(S2, b)
                        bump("after:$h2:" * (h2 in ("dead", "open") ? cat(S2, b) : "-"))
                        # qué se rompe: nodos de B que mueren (y si los mata el filtro directamente: su paso es el de
                        # un requisito de otro color) y aristas que faltan entre los vivos; y si los padres siguen vivos
                        reqs = s2[2]
                        for (i, x) in enumerate(b)
                            PG.is_alive(S2.og, x) && continue
                            direct = any(r -> r.step == x.id.step && r != x.id, reqs)
                            bump("broke:node$i:" * (direct ? "filter" : "cascade"))
                        end
                        for f in FACES
                            (PG.is_alive(S2.og, b[f[1]]) && PG.is_alive(S2.og, b[f[2]])) || continue
                            edge(S2, b[f[1]], b[f[2]]) || bump("broke:edge$(f[1])$(f[2])")
                        end
                        bump("broke:parents=" * string(count(p -> PG.is_alive(S2.og, p) && sig(S, p, b) != "---",
                                                             alive_at(S, T))))
                        bump("broke:reqsteps=" * join(sort([Int(r.step) - T for r in reqs]), ",") * "|bsteps=" *
                             join([st(x) - T for x in b], ","))
                    end
                end
            end
        end
        PG.FORBID[] = :off
        col(pre) = join(sort(["$(k[length(pre)+1:end]):$v" for (k, v) in C if startswith(k, pre)]), " ")
        return (truth, get(C, "news", 0), col("sigS:"), col("sigA:"), col("shapeA:"), col("next:"), col("after:"), col("broke:"),
                round(t, digits = 1))
    end
end

main()
