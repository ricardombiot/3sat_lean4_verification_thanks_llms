# GL con fijaciones (lean/improves_bin, LineUnion): ¿la unión de estados de una línea, cada uno filtrado por sus
# propios pins, sigue sin crear cliques con testigos?
#   GLW: caso de la ventana. Destino d = L3 con índice 0: la fuente con L2 = 1 filtrada por los requisitos de d y la
#        fuente con L2 = 0 filtrada por los requisitos de d y L1 = 1.
#   GLP: fijaciones cualesquiera: cada estado filtrado por un nodo de mapa (de pasos < n) elegido al azar, 3 sorteos.
#   julia --project=../.. glpin_probe.jl [--k3] f1.cnf ...
include("./../../src/main.jl")
using Random
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
good(U, B, Q, top) = isclique(U, Q) && all(l -> any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[])), 0:top)
function check!(st, tag, gs, nv, k3)
    gs = [g for g in gs if g.is_valid]
    length(gs) >= 2 || return
    Us = [tables!(Dict{PathNodeId, Set{PathNodeId}}(), g) for g in gs]; Bs = [bystep_of(u) for u in Us]
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for u in Us; for (r, S) in u; union!(get!(U, r, Set{PathNodeId}()), S); end; end
    B = bystep_of(U); top = maximum(p.id.step for p in keys(U))
    nodes = collect(keys(U)); Qs = [[x] for x in nodes]
    for i in eachindex(nodes), k in i+1:length(nodes)
        nodes[i].id.step == nodes[k].id.step && continue
        owns(U, nodes[i], nodes[k]) && push!(Qs, [nodes[i], nodes[k]])
    end
    if k3
        for i in eachindex(nodes), k in i+1:length(nodes), j in k+1:length(nodes)
            length(Set([nodes[i].id.step, nodes[k].id.step, nodes[j].id.step])) == 3 || continue
            Q = [nodes[i], nodes[k], nodes[j]]; isclique(U, Q) && push!(Qs, Q)
        end
    end
    for Q in Qs
        good(U, B, Q, top) || continue
        st["$tag Q"] = get(st, "$tag Q", 0) + 1
        k = any(i -> good(Us[i], Bs[i], Q, top), eachindex(gs)) ? "$tag ok" : "$tag FALLA"
        st[k] = get(st, k, 0) + 1
    end
end
function probe(path, st, k3)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    rng = MersenneTwister(7)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        states = Any[]
        CollectionTimeline.for_each_gpath(m.timeline, s, g -> (g.is_valid && push!(states, g)))
        if length(states) >= 2
            # GLW: destinos L3 con índice 0 alcanzables desde ambas fuentes
            ds = unique([d for g in states for d in SatMachine.map_get_node(gmap, g.map_parent_id).sons])
            for d in ds
                (d.index == 0 && d.step > 2nv + 1 && (d.step - 2nv - 2) % 3 == 2) || continue
                dn = SatMachine.map_get_node(gmap, d)
                gs = Any[]
                for g in states
                    d in SatMachine.map_get_node(gmap, g.map_parent_id).sons || continue
                    f = deepcopy(g)
                    pins = Set(dn.requires)
                    g.map_parent_id.index == 0 && push!(pins, (step = s - 1, index = 1))
                    redirect_stdout(devnull) do; GraphPath.filter!(f, pins); end
                    push!(gs, f)
                end
                check!(st, "GLW", gs, nv, k3)
            end
            # GLP: pins al azar
            for _ in 1:3
                gs = Any[]
                for g in states
                    f = deepcopy(g)
                    t = rand(rng, 0:s-1); ids = GraphMapBin.get_ids_step(gmap, Step(t))
                    redirect_stdout(devnull) do; GraphPath.filter!(f, Set([rand(rng, collect(ids))])); end
                    push!(gs, f)
                end
                check!(st, "GLP", gs, nv, k3)
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
