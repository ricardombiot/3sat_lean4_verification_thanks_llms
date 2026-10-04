# Certificados filtrados (sustituto de MapCert tras certj_probe.jl: MapCert J falla con R en el paso n).
#   FC-J: Q clique con testigos en un estado de línea g ⇒ cadena de g por Q (R vacío).
#   FC-P: Q clique con testigos en la pieza upF g d (filtro por reqOf d + up) ⇒ cadena de la pieza por Q.
#   julia --project=../.. fcert_probe.jl f1.cnf ...
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
function chain(U, B, fixed, top)
    sel = Dict{Int, PathNodeId}()
    function go(l)
        l < 0 && return true
        for c in (haskey(fixed, l) ? fixed[l] : get(B, l, PathNodeId[]))
            haskey(U, c) || continue
            all(p -> owns(U, c, p) && owns(U, p, c), values(sel)) || continue
            sel[l] = c
            go(l - 1) && return true
            delete!(sel, l)
        end
        false
    end
    go(top)
end
function check(U, top, tag, st, name)
    B = bystep_of(U); ns = collect(keys(U)); Qs = [[x] for x in ns]
    for i in eachindex(ns), k in i+1:length(ns)
        ns[i].id.step == ns[k].id.step && continue
        owns(U, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
    end
    for Q in Qs
        good(U, B, Q, top) || continue
        fixed = Dict(q.id.step => [q] for q in Q)
        ok = chain(U, B, fixed, top)
        st["$tag $(ok ? "ok" : "FALLA")"] = get(st, "$tag $(ok ? "ok" : "FALLA")", 0) + 1
        ok || get(st, "ej $tag", 0) >= 3 || (st["ej $tag"] = get(st, "ej $tag", 0) + 1; println("$tag sin cadena: $name Q=$Q"))
    end
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            check(tables(g), s, "FC-J", st, "$(basename(path)) paso $s")
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && check(tables(p), s + 1, "FC-P", st, "$(basename(path)) paso $(s+1) pieza")
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
