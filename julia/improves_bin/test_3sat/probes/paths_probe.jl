# ¿Inventa caminos la unión? En cada join, recorre los caminos completos del estado unido (nodos enlazados por
# `parents`, de un nodo del paso nuevo hasta la raíz) y comprueba si están enteros en una sola pieza:
#   P1: nodos y enlaces en una misma pieza;  P2: además, cadena (cada nodo posee a todos los demás) en el unido;
#   P3: si es cadena en el unido, también es cadena dentro de una pieza.
#   julia --project=../.. paths_probe.jl f1.cnf ...
include("./../../src/main.jl")
function nodesmap(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; D[pid] = node; end
    D
end
owns(D, r, q) = haskey(D, r) && haskey(D[r].owners.table, q.id.step) && (q in D[r].owners.table[q.id.step])
linked(D, a, b) = haskey(D, a) && (b in D[a].parents)   # b es padre de a
function paths(D, top, cap)
    out = Vector{Vector{PathNodeId}}()
    function go(p)
        length(out) >= cap && return
        last = p[end]
        if last.id.step == 0; push!(out, copy(p)); return; end
        for c in D[last].parents
            haskey(D, c) || continue
            push!(p, c); go(p); pop!(p)
        end
    end
    for t in top; go([t]); end
    out
end
chain(D, p) = all(a -> all(b -> a == b || owns(D, a, b), p), p)
function main(args)
    st = Dict{String, Int}(); bump(k) = (st[k] = get(st, k, 0) + 1)
    for path in args
        gmap = GraphMapBin.load_import_bin!(path)
        m = SatMachine.new(gmap); SatMachine.init!(m)
        while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
            s = m.current_step
            pieces = Dict{NodeId, Vector{Any}}()
            CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
                node = SatMachine.map_get_node(gmap, g.map_parent_id)
                for d in node.sons
                    dn = SatMachine.map_get_node(gmap, d)
                    p = deepcopy(g)
                    redirect_stdout(devnull) do
                        GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                    end
                    p.is_valid && push!(get!(pieces, d, Any[]), p)
                end
            end)
            redirect_stdout(devnull) do; SatMachine.make_step!(m); end
            s1 = m.current_step
            CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
                ps = get(pieces, g.map_parent_id, Any[])
                length(ps) >= 2 || return
                D = nodesmap(g); Dp = [nodesmap(p) for p in ps]
                top = [pid for pid in keys(D) if pid.id.step == s1]
                for p in paths(D, top, 20000)
                    bump("caminos del unido")
                    inone = any(i -> all(k -> k == length(p) || linked(Dp[i], p[k], p[k+1]), 1:length(p)), eachindex(Dp))
                    bump(inone ? "P1 ok: camino entero en una pieza" : "P1 FALLA: camino que mezcla piezas")
                    if chain(D, p)
                        bump("  cadena en el unido")
                        bump(any(i -> all(k -> k == length(p) || linked(Dp[i], p[k], p[k+1]), 1:length(p)) && chain(Dp[i], p), eachindex(Dp)) ?
                             "  P3 ok: cadena también dentro de una pieza" : "  P3 FALLA: cadena solo en el unido")
                    end
                end
            end)
        end
        println("$(basename(path)) listo")
    end
    for (k, v) in sort(collect(st)); println("  $k: $v"); end
end
main(ARGS)
