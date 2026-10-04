# Las cimas de una entrada frente a la entrada de su abuelo, dos líneas atrás (1-oct-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_topback.jl <salida.tsv>
#
# Con FORBID = :on. El nacimiento de PrevCut (probe_birth.jl) se ve, dos líneas atrás, sin tríos: la entrada del color
# del abuelo de un padre no tiene una arista o un nodo de la base. Aquí se miden los dos enunciados sueltos, sin el
# contexto de la base, sobre TODAS las entradas `a` (línea T, clave k) y sus cimas `p = (k, c, g)`, con `E` la entrada
# de clave `g` de la línea T-2:
#
# TopFull — un nodo `v` vivo en `a` y en `E` (paso < T-2) es vecino de `p` en `a`.
#   tf / tf_fail          todas las parejas (p, v)
#   tfs / tfs_fail        solo si `v` es vecino en `a` de la otra cima hermana (k, c, g'), g' ≠ g
# TopEdge — un trío `(p, u, w)` prohibido en `a` (con sus tres aristas, `u`, `w` de paso < T-2): `E` no tiene la
#   arista u–w.
#   te / te_fail          todos los tríos
#   tes / tes_fail        solo si la cima hermana sostiene la cara (u, w) en `a`
#   te_how                cómo está (u, w) en E en los fallos: los dos nodos y la arista están («edge»)

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
holds(g, p, u, w) = edge(g, p, u) && edge(g, p, w) && edge(g, u, w) && !PG.dead_trio(g.og, p, u, w)

function main()
    _, loader, _ = ProbeLib.map_of_env()
    keys = ("entries", "tf", "tf_fail", "tfs", "tfs_fail", "te", "te_fail", "tes", "tes_fail")
    header = "instance\ttruth\t" * join(keys, "\t") * "\tsecs"
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
            for s in SENDS
                get!(get!(lines, Int(s[1].current_step), Dict{Any, Any}()), s[1].map_parent_id, s[1])
            end
            for (T, es) in lines, (k, a) in es
                T >= 3 || continue
                bump("entries")
                l2 = get(lines, T - 2, Dict{Any, Any}())
                tops = alive_at(a, T - 1)
                olds = [v for l in 0:(T - 3) for v in alive_at(a, l)]
                for p in tops
                    E = get(l2, p.gparent_id, nothing)
                    E === nothing && continue
                    sibs = [q for q in tops if q != p && q.parent_id == p.parent_id]
                    # TopFull
                    for v in olds
                        PG.is_alive(E.og, v) || continue
                        sib = any(q -> edge(a, q, v), sibs)
                        bump("tf"); sib && bump("tfs")
                        if !edge(a, p, v)
                            bump("tf_fail"); sib && bump("tfs_fail")
                        end
                    end
                    # TopEdge: los tríos prohibidos con la cima `p`
                    nb = [v for v in olds if edge(a, p, v)]
                    for i in 1:length(nb), j in (i + 1):length(nb)
                        u, w = nb[i], nb[j]
                        (edge(a, u, w) && PG.dead_trio(a.og, p, u, w)) || continue
                        sib = any(q -> holds(a, q, u, w), sibs)
                        bump("te"); sib && bump("tes")
                        if edge(E, u, w)
                            bump("te_fail"); sib && bump("tes_fail")
                        end
                    end
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, k, 0) for k in keys)..., round(t, digits = 1))
    end
end

main()
