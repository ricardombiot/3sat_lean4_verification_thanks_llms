# Inducción de GLF (lean/improves_bin, LineUnion):
#   GLF*: familia al azar de estados de la línea, cada uno con pins al azar (un estado puede repetirse con pins
#         distintos): la unión no crea cliques con testigos.
#   FU:   filtrar el estado unido J por pins ps cabe, entrada a entrada, en la unión de las piezas filtradas por ps.
#   julia --project=../.. glfstar_probe.jl f1.cnf ...
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
function filt(g, pins)
    f = deepcopy(g); redirect_stdout(devnull) do; GraphPath.filter!(f, Set(pins)); end; f
end
randpins(rng, gmap, s) = s <= 0 ? NodeId[] : [rand(rng, collect(GraphMapBin.get_ids_step(gmap, Step(t)))) for t in rand(rng, 0:s-1, rand(rng, 0:2))]
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    rng = MersenneTwister(11)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        states = Any[]; pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            push!(states, g)
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
        # GLF*: 3 familias de 3 a 4 miembros
        for _ in 1:3
            isempty(states) && break
            fam = [filt(rand(rng, states), randpins(rng, gmap, s)) for _ in 1:rand(rng, 3:4)]
            fam = [f for f in fam if f.is_valid]
            length(fam) >= 2 || continue
            Us = [tables!(Dict{PathNodeId, Set{PathNodeId}}(), f) for f in fam]; Bs = [bystep_of(u) for u in Us]
            U = Dict{PathNodeId, Set{PathNodeId}}()
            for u in Us; for (r, S) in u; union!(get!(U, r, Set{PathNodeId}()), S); end; end
            B = bystep_of(U); top = s - 1
            nodes = collect(keys(U))
            Qs = [[x] for x in nodes]
            for i in eachindex(nodes), k in i+1:length(nodes)
                nodes[i].id.step == nodes[k].id.step && continue
                owns(U, nodes[i], nodes[k]) && push!(Qs, [nodes[i], nodes[k]])
            end
            for Q in Qs
                good(U, B, Q, top) || continue
                bump("GLF* Q")
                bump(any(i -> good(Us[i], Bs[i], Q, top), eachindex(fam)) ? "GLF* ok" : "GLF* FALLA")
            end
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        # FU
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            for _ in 1:3
                pins = randpins(rng, gmap, s1)
                fJ = filt(g, pins); fJ.is_valid || continue
                UJ = tables!(Dict{PathNodeId, Set{PathNodeId}}(), fJ)
                UP = Dict{PathNodeId, Set{PathNodeId}}()
                for p in ps
                    fp = filt(p, pins); fp.is_valid || continue
                    for (r, S) in tables!(Dict{PathNodeId, Set{PathNodeId}}(), fp); union!(get!(UP, r, Set{PathNodeId}()), S); end
                end
                ok = all(((r, S),) -> haskey(UP, r) && issubset(S, UP[r]), UJ)
                bump(ok ? "FU ok" : "FU FALLA")
            end
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
