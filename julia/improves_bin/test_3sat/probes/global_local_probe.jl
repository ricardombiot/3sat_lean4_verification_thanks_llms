# Invariante no local: la unión de TODOS los estados de una línea (sin claves). ¿Una clique con testigos de esa
# unión vive, con sus testigos, en un solo estado de la línea? (GL). Si vale, el join (unión de dos piezas) es un
# caso particular, y el invariante podría pasar de una línea a la siguiente.
#   GL:  clique con testigos en la unión de la línea ⇒ clique con testigos en algún estado de la línea
#   GLs: lo mismo para la unión de cada subconjunto de 2 estados de la línea
#   julia --project=../.. global_local_probe.jl [--k3] f1.cnf ...
include("./../../src/main.jl")
function tables!(U, g)
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
function bystep_of(U)
    b = Dict{Int, Vector{PathNodeId}}()
    for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end
    b
end
haswit(U, B, Q, top) = all(l -> any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[])), 0:top)
good(U, B, Q, top) = isclique(U, Q) && haswit(U, B, Q, top)
function cliques(U, nv, k3)
    nodes = collect(keys(U)); Qs = [[x] for x in nodes]
    for i in eachindex(nodes), k in i+1:length(nodes)
        nodes[i].id.step == nodes[k].id.step && continue
        owns(U, nodes[i], nodes[k]) && push!(Qs, [nodes[i], nodes[k]])
    end
    if k3
        vn = [x for x in nodes if 1 <= x.id.step <= 2nv]
        for i in eachindex(vn), k in i+1:length(vn), j in k+1:length(vn)
            length(Set([vn[i].id.step, vn[k].id.step, vn[j].id.step])) == 3 || continue
            push!(Qs, [vn[i], vn[k], vn[j]])
        end
    end
    Qs
end
function probe(path, st; k3 = false)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while true
        s = m.current_step
        states = Any[]
        CollectionTimeline.for_each_gpath(m.timeline, s, g -> (g.is_valid && push!(states, g)))
        if length(states) >= 2
            Us = [tables!(Dict{PathNodeId, Set{PathNodeId}}(), g) for g in states]
            Bs = [bystep_of(u) for u in Us]
            top = maximum(p.id.step for u in Us for p in keys(u))
            for (tag, idx) in vcat([("GL", collect(eachindex(states)))],
                                   [("GLs", [i, j]) for i in eachindex(states) for j in i+1:length(states)])
                U = Dict{PathNodeId, Set{PathNodeId}}()
                for i in idx; for (r, S) in Us[i]; union!(get!(U, r, Set{PathNodeId}()), S); end; end
                B = bystep_of(U)
                for Q in cliques(U, nv, k3)
                    good(U, B, Q, top) || continue
                    bump("$tag Q con testigos")
                    bump(any(i -> good(Us[i], Bs[i], Q, top), idx) ? "$tag ok" : "$tag FALLA")
                end
            end
        end
        # AP: la unión de TODAS las piezas (todos los destinos) de esta línea
        pieces = Any[]
        for g in states
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(pieces, p)
            end
        end
        if length(pieces) >= 2
            Up = [tables!(Dict{PathNodeId, Set{PathNodeId}}(), p) for p in pieces]
            Bp = [bystep_of(u) for u in Up]
            topp = maximum(p.id.step for u in Up for p in keys(u))
            U = Dict{PathNodeId, Set{PathNodeId}}()
            for u in Up; for (r, S) in u; union!(get!(U, r, Set{PathNodeId}()), S); end; end
            B = bystep_of(U)
            bump("AP piezas por paso = $(length(pieces))")
            for Q in cliques(U, nv, k3)
                good(U, B, Q, topp) || continue
                bump("AP Q con testigos")
                bump(any(i -> good(Up[i], Bp[i], Q, topp), eachindex(pieces)) ? "AP ok" : "AP FALLA")
                # Wd: por destino. Para cada testigo de la cima w (destino d = w.id), ¿hay testigo en cada paso
                # dentro de la unión de las piezas de destino d?
                length(Set(p.map_parent_id for p in pieces)) >= 2 || continue
                bump("  Wd Q en paso con 2 destinos")
                tops = [w for w in get(B, topp, PathNodeId[]) if all(q -> owns(U, w, q), Q)]
                for w in tops
                    idx = [i for i in eachindex(pieces) if pieces[i].map_parent_id == w.id]
                    Ud = Dict{PathNodeId, Set{PathNodeId}}()
                    for i in idx; for (r, S) in Up[i]; union!(get!(Ud, r, Set{PathNodeId}()), S); end; end
                    Bd = bystep_of(Ud)
                    bump(haswit(Ud, Bd, Q, topp) ? "  Wd ok: testigos en todo paso dentro del destino de w" : "  Wd FALLA")
                    bump(good(Ud, Bd, Q, topp) ? "  Gd ok: Q buena en la unión del destino de w" : "  Gd FALLA")
                end
                dgood = unique([pieces[i].map_parent_id for i in eachindex(pieces) if good(Up[i], Bp[i], Q, topp)])
                bump(length(dgood) == 1 ? "  destinos buenos = 1" : "  destinos buenos = $(length(dgood))")
            end
        end
        (SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m)) && break
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}(); k3 = "--k3" in ARGS
for f in filter(a -> !startswith(a, "--"), ARGS)
    try probe(f, st; k3 = k3) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
