# Los 20 casos: clique Q con testigos en el estado unido J cuyos testigos poseen todos un nodo con la clave k_i de
# una pieza P_i, pero Q no es buena en P_i. Volcamos qué falla y si hay alguna solución (cadena) que pase por Q y k_i.
#   julia --project=../.. twenty_probe.jl f1.cnf ...
include("./../../src/main.jl")
key(p) = "$(p.id.step):$(p.id.index)"
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
function bystep_of(U)
    b = Dict{Int, Vector{PathNodeId}}()
    for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end
    b
end
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function probe(path, st)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    kindof(l, top) = l == 0 ? "raíz" : l <= 2nv ? "var" : l == 2nv + 1 ? "mid" : l == top ? "cima" : "L$((l - (2nv + 2)) % 3 + 1)"
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
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
            U = tables(g); B = bystep_of(U)
            Up = [tables(p) for (_, p) in ps]; Bp = [bystep_of(u) for u in Up]
            ns = collect(keys(U)); Qs = [[x] for x in ns]
            for i in eachindex(ns), k in i+1:length(ns)
                ns[i].id.step == ns[k].id.step && continue
                push!(Qs, [ns[i], ns[k]])
            end
            for Q in Qs
                good(U, B, Q, s1) || continue
                for (i, (k, _)) in enumerate(ps)
                    wk(l) = any(r -> all(q -> owns(U, r, q), Q) && any(v -> v.id == k, U[r]), get(B, l, PathNodeId[]))
                    all(l -> wk(l), 0:s1) || continue
                    good(Up[i], Bp[i], Q, s1) && continue
                    st[1] += 1
                    st[1] <= 4 || continue
                    println("── $(basename(path)) paso $s1 Q=$(map(key, Q)) clave k=$(k.step):$(k.index)")
                    println("   ¿Q clique en P_i? $(isclique(Up[i], Q))")
                    miss = [l for l in 0:s1 if !wit(Up[i], Bp[i], Q, l)]
                    println("   pasos sin testigo en P_i: $(map(l -> "$l($(kindof(l, s1)))", miss))")
                    goodj = [j for j in eachindex(ps) if good(Up[j], Bp[j], Q, s1)]
                    println("   piezas buenas: $(map(j -> "$(ps[j][1].step):$(ps[j][1].index)", goodj))")
                    # los testigos en J que poseen Q y un nodo k: ¿de qué pieza viene cada entrada?
                    for l in miss
                        for r in get(B, l, PathNodeId[])
                            all(q -> owns(U, r, q), Q) && any(v -> v.id == k, U[r]) || continue
                            src = [(j, [key(q) for q in Q if owns(Up[j], r, q)], any(v -> v.id == k, get(Up[j], r, Set{PathNodeId}()))) for j in eachindex(ps)]
                            println("     testigo $(key(r)) en paso $l: por pieza (Q poseídos, posee k): $src")
                        end
                    end
                end
            end
        end)
    end
end
st = [0]
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
println("casos: $(st[1])")
