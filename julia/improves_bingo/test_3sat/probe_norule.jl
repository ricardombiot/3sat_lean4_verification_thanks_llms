# ¿Prohíbe la llegada triángulos viejos? (1-oct-2026, rama reader-stuck)
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_norule.jl <salida.tsv>
#
# Con FORBID = :on, sobre TODAS las llegadas válidas S = arrOn a d. Un triángulo viejo (sus tres nodos por debajo del
# paso de `a`, o sea vivos antes del UP) prohibido en S solo puede venir de `a` o de la regla del review (del filtro o
# del UP): `up_forbid` solo escribe tríos con la cima nueva. `HNoRule` (lean ForbidOnHi.lean) dice que ya estaba
# prohibido en `a` si es de la zona «top» o de la categoría f3 (base muerta bajo una cima de S). Sin esa restricción
# es FALSO: v6_c26_i1 tiene 16 triángulos low:f2 que prohíbe la regla.
#
#   old_dead          triángulos viejos prohibidos en S
#   rule_new          los que en `a` son un triángulo sin prohibir (los prohíbe la regla)
#   cats              por categoría «zona:cat=prohibidos/de la regla»: zona «top» si el triángulo tiene un nodo en la
#                     cima de `a`, «low» si no; cat = la mejor cima de S vecina de los tres («nostar» si ninguna, o
#                     f0…f3 = el máximo de caras con esa cima sin prohibir)

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
    header = "instance\ttruth\told_dead\trule_new\tcats\tsecs"
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
            for s in SENDS
                a = s[1]
                T = Int(a.current_step)
                S = arrival(s)
                S.is_valid || continue
                for b in dead_tris(S)
                    maximum(st, b) < T || continue
                    zone = maximum(st, b) == T - 1 ? "top" : "low"
                    c = cat(S, b)
                    bump("old_dead"); bump("$zone:$c:dead")
                    if !(tri(a, b) && PG.dead_trio(a.og, b[1], b[2], b[3]))
                        bump("rule_new"); bump("$zone:$c:new")
                    end
                end
            end
        end
        PG.FORBID[] = :off
        cs = String[]
        for zone in ("top", "low"), c in ("nostar", "f0", "f1", "f2", "f3")
            d = get(C, "$zone:$c:dead", 0)
            d > 0 && push!(cs, "$zone:$c=$d/$(get(C, "$zone:$c:new", 0))")
        end
        return (truth, get(C, "old_dead", 0), get(C, "rule_new", 0), join(cs, " "), round(t, digits = 1))
    end
end

main()
