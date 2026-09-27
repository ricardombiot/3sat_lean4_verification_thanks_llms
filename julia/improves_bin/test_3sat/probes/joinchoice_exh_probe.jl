# Exhaustivo (cliques de un nodo) de JoinChoiceP y, en sus fallos, de TriP del estado unido. docs/context/ambfar.md §4.2ξ.
#   julia --project=../.. joinchoice_exh_probe.jl f1.cnf ...
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
isclique(U, Q) = all(q -> haskey(U, q) && all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
ownsall(U, y, P) = haskey(U, y) && all(p -> owns(U, y, p), P)
cxp(U, B, P, y, w, top) = owns(U, y, w) && haskey(U, w) &&
    all(l -> any(r -> owns(U, y, r) && owns(U, w, r) && ownsall(U, r, P), get(B, l, PathNodeId[])), 0:top)
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
                p.is_valid && push!(get!(pieces, d, Any[]), tables(p))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            Ts = get(pieces, g.map_parent_id, Any[])
            length(Ts) >= 2 || return
            U = tables(g); B = bystep_of(U); ns = collect(keys(U)); Bs = [bystep_of(T) for T in Ts]
            for x in ns
                P = [x]
                NP_ = [y for y in ns if owns(U, y, x)]
                for y in NP_, w in NP_
                    (y != w && cxp(U, B, P, y, w, top)) || continue
                    ok = any(i -> isclique(Ts[i], P) && ownsall(Ts[i], y, P) && ownsall(Ts[i], w, P) &&
                                  cxp(Ts[i], Bs[i], P, y, w, top), eachindex(Ts))
                    bump("JOINCHOICEP $(ok ? "ok" : "FALLA")")
                    if !ok
                        tj = all(l2 -> any(r -> owns(U, y, r) && owns(U, w, r) && ownsall(U, r, P) &&
                                           cxp(U, B, P, y, r, top) && cxp(U, B, P, w, r, top), get(B, l2, PathNodeId[])), 0:top)
                        bump("en los fallos, TriP del estado unido $(tj ? "ok" : "FALLA")")
                    end
                end
            end
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
