# Vía de caminos: ¿todo nodo está en una cadena? (lean/improves_bin: SupportedG, chain_in_piece)
#   S1: el estado tiene alguna cadena;  S2: todo nodo está en una cadena;  S3: toda entrada (r posee q) está en
#   una cadena que pasa por r y por q.
# En cada estado de cada línea de la máquina, y en los estados del lector: estado final filtrado por uno y por dos
# pins (nodos de mapa de pasos distintos) y revisado.
#   julia --project=../.. supported_probe.jl f1.cnf ...
include("./../../src/main.jl")
function nodesmap(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; D[pid] = node; end
    D
end
owns(D, r, q) = haskey(D, r) && haskey(D[r].owners.table, q.id.step) && (q in D[r].owners.table[q.id.step])
# cadenas: caminos por `parents` de un nodo del paso superior a la raíz, con posesión mutua de todos los nodos
function cover(D, top)
    covered = Set{PathNodeId}(); pairs = Set{Tuple{PathNodeId, PathNodeId}}(); nchains = Ref(0)
    function go(p)
        nchains[] >= 50000 && return
        last = p[end]
        if last.id.step == 0
            nchains[] += 1
            for a in p; push!(covered, a); for b in p; push!(pairs, (a, b)); end; end
            return
        end
        for c in D[last].parents
            haskey(D, c) || continue
            all(a -> owns(D, a, c) && owns(D, c, a), p) || continue
            push!(p, c); go(p); pop!(p)
        end
    end
    for t in top; go([t]); end
    covered, pairs, nchains[]
end
function check!(st, tag, g)
    g.is_valid || return
    D = nodesmap(g)
    isempty(D) && return
    s = maximum(p.id.step for p in keys(D))
    top = [p for p in keys(D) if p.id.step == s]
    cov, prs, nc = cover(D, top)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    bump("$tag estados")
    bump(nc > 0 ? "$tag S1 ok" : "$tag S1 FALLA: sin cadena")
    bump(length(cov) == length(D) ? "$tag S2 ok" : "$tag S2 FALLA: nodo fuera de toda cadena")
    ok3 = all(((r, n),) -> all(set -> all(q -> !haskey(D, q) || (r, q) in prs, set), values(n.owners.table)), D)
    bump(ok3 ? "$tag S3 ok" : "$tag S3 FALLA: entrada fuera de toda cadena")
end
function main(args)
    st = Dict{String, Int}()
    for path in args
        gmap = GraphMapBin.load_import_bin!(path)
        m = SatMachine.new(gmap); SatMachine.init!(m)
        while true
            CollectionTimeline.for_each_gpath(m.timeline, m.current_step, g -> check!(st, "línea", g))
            (SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m)) && break
            redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        end
        if SatMachine.have_solution(m)
            fin = first(SatMachine.get_gpath_solutions(m))
            ids = [id for s in 0:gmap.step-1 for id in GraphMapBin.get_ids_step(gmap, Step(s))]
            for (i, a) in enumerate(ids)
                g = deepcopy(fin); redirect_stdout(devnull) do; GraphPath.filter!(g, Set([a])); end
                check!(st, "lector 1 pin", g)
                for b in ids[i+1:end]
                    a.step == b.step && continue
                    g2 = deepcopy(fin); redirect_stdout(devnull) do; GraphPath.filter!(g2, Set([a, b])); end
                    check!(st, "lector 2 pins", g2)
                end
            end
        end
    end
    for (k, v) in sort(collect(st)); println("  $k: $v"); end
end
main(ARGS)
