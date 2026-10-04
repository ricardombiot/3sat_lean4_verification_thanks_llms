# Bajar un filtro con ancla (docs/context/escalera_reader.md §4.2λ). Estado de línea g (unidos incluidos) con cima `top`.
#   AF: Q buena en g con miembro w en la cima; en un paso l < top todas las entradas de w nombran el mismo nodo de mapa m
#       ⇒ Q buena en filterAll g [m]. (Sin ancla es falso: los 4 casos de certj_probe.jl.)
#   julia --project=../.. anchfilt_probe.jl f1.cnf ...
include("./../../src/main.jl")
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            U = tables(g); B = bystep_of(U)
            ns = collect(keys(U)); cache = Dict{NodeId, Any}()
            function fl(mid)
                get!(cache, mid) do
                    p = deepcopy(g)
                    redirect_stdout(devnull) do; GraphPath.filter!(p, Set([mid])); end
                    p.is_valid || return nothing
                    T = tables(p); (T, bystep_of(T))
                end
            end
            for w in get(B, top, PathNodeId[])
                fixed = NodeId[]
                for l in 0:top-1
                    idsl = unique([v.id for v in U[w] if v.id.step == l])
                    length(idsl) == 1 && push!(fixed, idsl[1])
                end
                for Q in vcat([[w]], [[w, q] for q in ns if q.id.step < top && owns(U, w, q)])
                    good(U, B, Q, top) || continue
                    for mid in fixed
                        r = fl(mid)
                        ok = r !== nothing && good(r[1], r[2], Q, top)
                        bump(ok ? "AF ok" : "AF FALLA")
                        ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("AF: $(basename(path)) paso $top Q=$Q m=$mid"))
                    end
                end
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
