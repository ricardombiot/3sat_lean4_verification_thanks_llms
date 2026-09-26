# Testigo coherente con su clave (docs/context/ambfar.md §4.2κ.8, candidato 1).
#   Estado unido J, piezas p_i con clave k_i (nodo fuente en el paso n). Q buena en J (clique + testigo en cada paso).
#   GLK:  en cada paso ∃ testigo r y ∃ i: r posee en J un nodo de id k_i y r posee Q en la pieza p_i.
#   GLKs: igual pero r posee Q y el nodo k_i dentro de la misma pieza p_i.
#   GLKany: ∃ i fijo para todos los pasos (una sola pieza con Q buena) — referencia.
#   julia --project=../.. key_probe.jl f1.cnf ...
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
ownsid(U, r, m) = any(v -> v.id == m, get(U, r, Set{PathNodeId}()))
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep(U) = (B = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(B, r.id.step, PathNodeId[]), r); end; B)
function pairsQ(U)
    ns = collect(keys(U)); Qs = [[x] for x in ns]
    for i in eachindex(ns), k in i+1:length(ns)
        ns[i].id.step == ns[k].id.step && continue
        owns(U, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
    end
    Qs
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(get!(pieces, d, Any[]), (g.map_parent_id, p))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            U = tables(g); B = bystep(U)
            ks = [k for (k, _) in ps]; Tp = [tables(p) for (_, p) in ps]
            for Q in pairsQ(U)
                isclique(U, Q) || continue
                all(l -> any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[])), 0:s1) || continue
                bump("Q buenas")
                cand(r, i, strict) = ownsid(strict ? Tp[i] : U, r, ks[i]) && all(q -> owns(Tp[i], r, q), Q)
                for (tag, strict) in (("GLK", false), ("GLKs", true))
                    ok = all(l -> any(r -> any(i -> cand(r, i, strict), eachindex(ps)), get(B, l, PathNodeId[])), 0:s1)
                    bump(ok ? "$tag ok" : "$tag FALLA")
                    if !ok && get(st, "$tag ej", 0) < 3
                        bump("$tag ej"); println("$tag FALLA: $(basename(path)) paso $s1 Q=$Q claves=$ks")
                    end
                end
                one = any(i -> isclique(Tp[i], Q) && all(l -> any(r -> all(q -> owns(Tp[i], r, q), Q), get(B, l, PathNodeId[])), 0:s1), eachindex(ps))
                bump(one ? "GLKany ok" : "GLKany FALLA")
            end
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
