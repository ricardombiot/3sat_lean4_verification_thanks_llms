# ¿Qué decide el destino bueno? (lean/improves_bin, invariante de unión de línea, docs/context/ambfar.md §4.2κ)
# En pasos con 2 destinos, para cada clique Q con testigos en la unión de todas las piezas y cada destino d:
#   good_d: Q clique con testigos en la unión de las piezas de d (J_d)
#   B1: Q clique en J_d y testigos en J_d en todos los pasos L3 anteriores     (análogo de H19)
#   B3: todo miembro de Q posee, en la unión, un nodo de cada requisito de d  (Q compatible con d)
#   B4: algún testigo de la cima de destino d posee Q en J_d y Q es clique en J_d
# y, si d es malo, qué falla: la clique o el testigo en qué tipo de paso.
#   julia --project=../.. dest_probe.jl f1.cnf ...
include("./../../src/main.jl")
const K3 = Ref("--k3" in ARGS)
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
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
function probe(path, st)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    kindof(l, top) = l == 0 ? "raíz" : l <= 2nv ? "var" : l == 2nv + 1 ? "mid" : l == top ? "cima" : "L$((l - (2nv + 2)) % 3 + 1)"
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Any[]; reqs = Dict{NodeId, Any}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d); reqs[d] = dn.requires
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(pieces, (d, tables!(Dict{PathNodeId, Set{PathNodeId}}(), p)))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        dests = unique(first.(pieces))
        length(dests) >= 2 || continue
        U = Dict{PathNodeId, Set{PathNodeId}}()
        for (_, u) in pieces; for (r, S) in u; union!(get!(U, r, Set{PathNodeId}()), S); end; end
        B = bystep_of(U); top = maximum(p.id.step for p in keys(U))
        Ud = Dict(d => (V = Dict{PathNodeId, Set{PathNodeId}}();
                        for (e, u) in pieces; e == d || continue; for (r, S) in u; union!(get!(V, r, Set{PathNodeId}()), S); end; end; V)
                  for d in dests)
        Bd = Dict(d => bystep_of(Ud[d]) for d in dests)
        nodes = collect(keys(U)); Qs = [[x] for x in nodes]
        for i in eachindex(nodes), k in i+1:length(nodes)
            nodes[i].id.step == nodes[k].id.step && continue
            owns(U, nodes[i], nodes[k]) && push!(Qs, [nodes[i], nodes[k]])
        end
        if K3[]
            vn = [x for x in nodes if 1 <= x.id.step]
            for i in eachindex(vn), k in i+1:length(vn), j in k+1:length(vn)
                length(Set([vn[i].id.step, vn[k].id.step, vn[j].id.step])) == 3 || continue
                isclique(U, [vn[i], vn[k], vn[j]]) && push!(Qs, [vn[i], vn[k], vn[j]])
            end
        end
        l3s = [l for l in 0:top-1 if kindof(l, top) == "L3"]
        for Q in Qs
            (isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)) || continue
            for d in dests
                V = Ud[d]; W = Bd[d]
                gd = isclique(V, Q) && all(l -> wit(V, W, Q, l), 0:top)
                b1 = isclique(V, Q) && all(l -> wit(V, W, Q, l), l3s)
                b3 = all(q -> all(rq -> any(v -> v.id == rq, get(U, q, Set{PathNodeId}())), reqs[d]), Q)
                b4 = isclique(V, Q) && any(w -> w.id == d && all(q -> owns(V, w, q), Q), get(W, top, PathNodeId[]))
                bump("Q tamaño $(length(Q)) $(gd ? "bueno" : "malo")")
                bump(gd == b1 ? "B1 ok: bueno ⇔ clique y testigos L3 en J_d" : "B1 FALLA")
                bump(gd == b3 ? "B3 ok: bueno ⇔ Q compatible con requisitos de d" : "B3 FALLA ($(gd ? "bueno" : "malo") y B3=$b3)")
                bump(gd == b4 ? "B4 ok: bueno ⇔ clique y top de d que posee Q en J_d" : "B4 FALLA")
                bump(gd == (b1 && b3) ? "B1∧B3 ok" : "B1∧B3 FALLA")
                if !gd
                    if !isclique(V, Q); bump("  malo: no es clique en J_d")
                    else
                        ks = Set(kindof(l, top) for l in 0:top if !wit(V, W, Q, l))
                        bump("  malo: sin testigo en " * join(sort(collect(ks)), "+"))
                    end
                end
            end
        end
    end
end
st = Dict{String, Int}()
for f in filter(a -> !startswith(a, "--"), ARGS)
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
