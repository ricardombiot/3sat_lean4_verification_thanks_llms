# Invariante corregido y bajada (lean/improves_bin, LineUnion; docs/context/escalera_reader.md §4.2κ.7).
#   GLJ: unión de los estados de una línea. Q clique entrada a entrada; en cada paso, un testigo r y UN estado donde r
#        posee a la vez Q y las restricciones R ⇒ Q buena (con R) en un solo estado. R ∈ {vacío, cima [m], bajo [c]}.
#   DJ:  estado unido J. Q buena con R en J ⇒ en cada paso, un testigo r y UNA pieza donde r posee Q y R juntos.
#        R ∈ {vacío, clave de una pieza [k_i]}.
#   julia --project=../.. joint_probe.jl f1.cnf ...
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
function uni(Ts)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for T in Ts; for (r, S) in T; union!(get!(U, r, Set{PathNodeId}()), S); end; end
    U
end
bystep(U) = (B = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(B, r.id.step, PathNodeId[]), r); end; B)
# r posee Q y un nodo de cada id de R en la tabla T
jown(T, r, Q, R) = all(q -> owns(T, r, q), Q) && all(m -> any(v -> v.id == m, get(T, r, Set{PathNodeId}())), R)
goodR(T, B, Q, R, top) = isclique(T, Q) && all(l -> any(r -> jown(T, r, Q, R), get(B, l, PathNodeId[])), 0:top)
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
                p.is_valid && push!(get!(pieces, d, Any[]), (g.map_parent_id, p))
            end
        end)
        # GLJ
        if length(states) >= 2
            Ts = [tables(g) for g in states]; Bs = [bystep(T) for T in Ts]
            U = uni(Ts); B = bystep(U); top = s
            Rs = vcat([NodeId[]], [[g.map_parent_id] for g in states],
                      [[c] for c in unique([r.id for r in keys(U) if 0 < r.id.step < top])])
            for Q in pairsQ(U), R in Rs
                isclique(U, Q) || continue
                hyp = all(l -> any(r -> any(i -> jown(Ts[i], r, Q, R), eachindex(Ts)), get(B, l, PathNodeId[])), 0:top)
                hyp || continue
                tag = isempty(R) ? "GLJ R=∅" : (R[1].step == top ? "GLJ R cima" : "GLJ R bajo")
                bump("$tag Q")
                bump(any(i -> goodR(Ts[i], Bs[i], Q, R, top), eachindex(Ts)) ? "$tag ok" : "$tag FALLA")
            end
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        # DJ
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            U = tables(g); B = bystep(U)
            Tp = [tables(p) for (_, p) in ps]
            for Q in pairsQ(U), R in vcat([NodeId[]], [[k] for (k, _) in ps])
                goodR(U, B, Q, R, s1) || continue
                tag = isempty(R) ? "DJ R=∅" : "DJ R=[k_i]"
                bump("$tag Q")
                ok = all(l -> any(r -> any(i -> jown(Tp[i], r, Q, R), eachindex(Tp)), get(B, l, PathNodeId[])), 0:s1)
                bump(ok ? "$tag ok" : "$tag FALLA")
            end
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
