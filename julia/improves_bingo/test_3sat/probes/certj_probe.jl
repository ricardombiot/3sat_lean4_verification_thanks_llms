# ¿MapCert J en los 20 casos? Q clique de J, WitR J Q [k] (k clave de una pieza, paso n), Q no buena en P_k.
# Busca una cadena (un nodo por paso 0..top, todos se poseen mutuamente en J) por Q y por un nodo de id k.
#   julia --project=../.. certj_probe.jl f1.cnf ...
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
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
# cadena: backtracking de arriba abajo con candidatos que poseen todo lo elegido
function chain(U, B, fixed, top)
    sel = Dict{Int, PathNodeId}()
    function go(l)
        l < 0 && return true
        cands = haskey(fixed, l) ? fixed[l] : get(B, l, PathNodeId[])
        for c in cands
            haskey(U, c) || continue
            all(p -> owns(U, c, p) && owns(U, p, c), values(sel)) || continue
            sel[l] = c
            go(l - 1) && return true
            delete!(sel, l)
        end
        false
    end
    go(top)
end
function probe(path, st)
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
                    all(wk, 0:s1) || continue
                    good(Up[i], Bp[i], Q, s1) && continue
                    fixed = Dict{Int, Vector{PathNodeId}}()
                    for q in Q; fixed[q.id.step] = [q]; end
                    ks = [v for v in get(B, k.step, PathNodeId[]) if v.id == k]
                    fixed[k.step] = haskey(fixed, k.step) ? filter(v -> v.id == k, fixed[k.step]) : ks
                    c = chain(U, B, fixed, s1 - 1)   # CertR mira pasos < current_step
                    st[c ? "CertR J ok" : "CertR J FALLA"] = get(st, c ? "CertR J ok" : "CertR J FALLA", 0) + 1
                    c || get(st, "ej", 0) >= 3 || (st["ej"] = get(st, "ej", 0) + 1; println("sin cadena: $(basename(path)) paso $s1 Q=$(map(key, Q)) k=$(k.step):$(k.index)"))
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
