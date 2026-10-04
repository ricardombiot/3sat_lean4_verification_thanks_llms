# ¿GL / GLF con una restricción en la cima (R = [m], m clave de un estado de la línea) se cumple?
#   GLtop: estados de la línea sin fijar (cada uno una vez). Q clique con testigos en la unión, todos los testigos
#          poseen un nodo de la cima con id m ⇒ Q clique con testigos (que posean m) en el estado de clave m.
#   GLFtop: lo mismo con cada estado fijado por los requisitos de un destino común d (y L1 = 1 si su filtro salta).
#   julia --project=../.. gltop_probe.jl [--k3] f1.cnf ...
include("./../../src/main.jl")
function nodes(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; D[pid] = node; end
    D
end
tab(n) = (S = Set{PathNodeId}(); for (_, set) in n.owners.table; union!(S, set); end; S)
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
function uni(Ts)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for T in Ts; for (r, S) in T; union!(get!(U, r, Set{PathNodeId}()), S); end; end
    U
end
function check!(st, tag, fam, top, k3)
    length(fam) >= 2 || return
    Ts = [Dict(r => tab(n) for (r, n) in nodes(f)) for (_, f) in fam]
    U = uni(Ts)
    B = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(B, r.id.step, PathNodeId[]), r); end
    ns = collect(keys(U)); Qs = [[x] for x in ns]
    for i in eachindex(ns), j in i+1:length(ns)
        ns[i].id.step == ns[j].id.step && continue
        owns(U, ns[i], ns[j]) && push!(Qs, [ns[i], ns[j]])
    end
    if k3
        for i in eachindex(ns), j in i+1:length(ns), l in j+1:length(ns)
            length(Set([ns[i].id.step, ns[j].id.step, ns[l].id.step])) == 3 || continue
            Q = [ns[i], ns[j], ns[l]]; isclique(U, Q) && push!(Qs, Q)
        end
    end
    # GLbelow: R = [c], c nodo de mapa de un paso bajo la cima
    cs_ = unique([r.id for r in keys(U) if r.id.step < top])
    for Q in Qs, c in cs_
        isclique(U, Q) || continue
        witc(V, l) = any(r -> all(q -> owns(V, r, q), Q) && any(t -> t.id == c && owns(V, r, t), keys(U)), get(B, l, PathNodeId[]))
        all(l -> witc(U, l), 0:top) || continue
        st["$tag-below Q"] = get(st, "$tag-below Q", 0) + 1
        ok = any(i -> isclique(Ts[i], Q) && all(l -> witc(Ts[i], l), 0:top), eachindex(fam))
        st["$tag-below $(ok ? "ok" : "FALLA")"] = get(st, "$tag-below $(ok ? "ok" : "FALLA")", 0) + 1
    end
    for Q in Qs, (k, _) in fam
        isclique(U, Q) || continue
        topk = [t for t in get(B, top, PathNodeId[]) if t.id == k]
        wit(V, l) = any(r -> all(q -> owns(V, r, q), Q) && any(t -> owns(V, r, t), topk), get(B, l, PathNodeId[]))
        all(l -> wit(U, l), 0:top) || continue
        st["$tag Q"] = get(st, "$tag Q", 0) + 1
        i = findfirst(x -> x[1] == k, fam); V = Ts[i]
        ok = isclique(V, Q) && all(l -> wit(V, l), 0:top)
        st["$tag $(ok ? "ok" : "FALLA")"] = get(st, "$tag $(ok ? "ok" : "FALLA")", 0) + 1
    end
end
function probe(path, st, k3)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        states = Any[]
        CollectionTimeline.for_each_gpath(m.timeline, s, g -> (g.is_valid && push!(states, g)))
        if length(states) >= 2
            check!(st, "GLtop", [(g.map_parent_id, g) for g in states], s, k3)
            ds = unique([d for g in states for d in SatMachine.map_get_node(gmap, g.map_parent_id).sons])
            for d in ds
                dn = SatMachine.map_get_node(gmap, d)
                fam = Any[]
                for g in states
                    d in SatMachine.map_get_node(gmap, g.map_parent_id).sons || continue
                    f = deepcopy(g); redirect_stdout(devnull) do; GraphPath.filter!(f, Set(dn.requires)); end
                    f.is_valid || continue
                    # ¿el filtro salta ventana hacia d? se detecta haciendo el UP
                    p = deepcopy(f)
                    skip = false
                    redirect_stdout(devnull) do
                        GraphPath.do_up!(p, d, dn.title, SatMachine.map_prohibited(gmap))
                    end
                    pins = Set(dn.requires)
                    if d.index == 0 && d.step > 2nv + 1 && (d.step - 2nv - 2) % 3 == 2 && g.map_parent_id.index == 0
                        push!(pins, (step = s - 1, index = 1))
                    end
                    f2 = deepcopy(g); redirect_stdout(devnull) do; GraphPath.filter!(f2, pins); end
                    f2.is_valid && push!(fam, (g.map_parent_id, f2))
                end
                check!(st, "GLFtop", fam, s, k3)
            end
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}(); k3 = "--k3" in ARGS
for f in filter(a -> !startswith(a, "--"), ARGS)
    try probe(f, st, k3) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
