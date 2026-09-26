# Localidad anclada en la unión de TODAS las piezas de un paso (todas las fuentes × destinos), sin filtro.
#   APA: Q buena en la unión con miembro w en la cima ⇒ Q buena en la pieza de w (fuente de clave w.parent_id,
#        destino w.id). Si vale, S2 sería un caso particular y podría llevarse por inducción de un paso al siguiente.
#   LUA: lo mismo en la unión de los estados de una línea (claves distintas): Q buena con miembro c en la cima ⇒ buena
#        en el estado de clave c.id.
#   julia --project=../.. apanchor_probe.jl f1.cnf ...
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
uni(Ts) = (U = Dict{PathNodeId, Set{PathNodeId}}(); for T in Ts, (r, S) in T; union!(get!(U, r, Set{PathNodeId}()), S); end; U)
function anchored(U, top, tag, owner, st, name)
    B = bystep_of(U)
    ns = collect(keys(U)); tops = get(B, top, PathNodeId[])
    for w in tops
        T = owner(w); T === nothing && (st["$tag sin dueño"] = get(st, "$tag sin dueño", 0) + 1; continue)
        Bt = bystep_of(T)
        cands = vcat([[w]], [[w, q] for q in ns if q.id.step < top && owns(U, w, q)])
        for Q in cands
            good(U, B, Q, top) || continue
            ok = good(T, Bt, Q, top)
            k = "$tag $(ok ? "ok" : "FALLA")"; st[k] = get(st, k, 0) + 1
            ok || get(st, "ej $tag", 0) >= 4 || (st["ej $tag"] = get(st, "ej $tag", 0) + 1; println("$tag: $name Q=$Q"))
        end
    end
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{Tuple{NodeId, NodeId}, Any}()
        states = Dict{NodeId, Any}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            states[g.map_parent_id] = tables(g)
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && (pieces[(g.map_parent_id, d)] = tables(p))
            end
        end)
        if length(states) >= 2
            anchored(uni(collect(values(states))), s, "LUA", c -> get(states, c.id, nothing), st, "$(basename(path)) paso $s")
        end
        if length(pieces) >= 2
            anchored(uni(collect(values(pieces))), s + 1, "APA",
                w -> w.parent_id === nothing ? nothing : get(pieces, (w.parent_id, w.id), nothing), st,
                "$(basename(path)) paso $(s+1)")
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
