# ¿El pin del lector y su review arreglan los fallos de JoinChoiceP en el estado unido J? Para cada fallo (P = [x], enlace
# y–w, cliques de un nodo, exhaustivo) se fija en una copia de J el nodo de mapa de x, de y o de w (GraphPath.filter!,
# review con pair mode incluido) y se mira: estado muerto, trío {x, y, w} roto (algún nodo o par ya no está) o trío vivo;
# si sigue vivo, si TriP vale ya en el estado fijado. También fijando dos de los tres, uno tras otro, como el lector. docs/context/escalera_reader.md §4.2ξ.
#   julia --project=../.. joinpin_probe.jl f1.cnf ...
include("./../../src/main.jl")
function read_cnf(path)
    nv = 0; cls = Vector{Vector{Int}}()
    for line in eachline(path)
        isempty(line) && continue
        c = line[1]
        (c == 'c' || c == '%') && continue
        if c == 'p'
            nv = parse(Int, split(line)[3])
        else
            lits = [parse(Int, t) for t in split(line) if t != "0"]
            length(lits) == 3 && push!(cls, lits)
        end
    end
    nv, cls
end

# selección de una asignación en cada paso (mapa bin, pasos 0-indexados)
function sel(a, s, nv, cls)
    if s == 0 || s == 2nv + 1 || s >= 2nv + 2 + 3length(cls)
        return (step = s, index = 0)
    elseif s <= 2nv
        v = (s + 1) ÷ 2
        return isodd(s) ? (step = s, index = Int(a[v])) : (step = s, index = 1 - Int(a[v]))
    else
        o = s - (2nv + 2); j = o ÷ 3 + 1; p = o % 3 + 1
        l = cls[j][p]
        val = l > 0 ? a[abs(l)] : !a[abs(l)]
        return (step = s, index = Int(val))
    end
end

function pid(a, s, nv, cls)
    p = s >= 1 ? sel(a, s - 1, nv, cls) : nothing
    g = s >= 2 ? sel(a, s - 2, nv, cls) : nothing
    PathNodeId(g, p, sel(a, s, nv, cls))
end

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
function nodesmap(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table; D[pid_] = node; end
    D
end
# ¿hay una cadena (por parents, con posesión mutua) de la cima a la raíz que pase por todos los de Q?
function chain_through(g, Q, top)
    D = nodesmap(g)
    own(r, q) = haskey(D, r) && haskey(D[r].owners.table, q.id.step) && (q in D[r].owners.table[q.id.step])
    need = Dict(q.id.step => q for q in Q)
    found = Ref(false); budget = Ref(2_000_000)
    function go(p)
        (found[] || budget[] <= 0) && return
        budget[] -= 1
        last = p[end]
        if last.id.step == 0; found[] = true; return; end
        for c in D[last].parents
            haskey(D, c) || continue
            haskey(need, c.id.step) && need[c.id.step] != c && continue
            all(a -> own(a, c) && own(c, a), p) || continue
            push!(p, c); go(p); pop!(p)
        end
    end
    for t in keys(D)
        t.id.step == top || continue
        haskey(need, top) && need[top] != t && continue
        go([t]); found[] && break
    end
    found[] ? "sí" : (budget[] <= 0 ? "presupuesto" : "no")
end
# versión mapa: cadena que pase por los nodos de mapa ids (cualquier nodo de camino con ese id)
function chain_through_map(g, ids, top)
    D = nodesmap(g)
    own(r, q) = haskey(D, r) && haskey(D[r].owners.table, q.id.step) && (q in D[r].owners.table[q.id.step])
    need = Dict(i.step => i for i in ids)
    found = Ref(false); budget = Ref(2_000_000)
    function go(p)
        (found[] || budget[] <= 0) && return
        budget[] -= 1
        last = p[end]
        if last.id.step == 0; found[] = true; return; end
        for c in D[last].parents
            haskey(D, c) || continue
            haskey(need, c.id.step) && need[c.id.step] != c.id && continue
            all(a -> own(a, c) && own(c, a), p) || continue
            push!(p, c); go(p); pop!(p)
        end
    end
    for t in keys(D)
        t.id.step == top || continue
        haskey(need, top) && need[top] != t.id && continue
        go([t]); found[] && break
    end
    found[] ? "sí" : (budget[] <= 0 ? "presupuesto" : "no")
end
function probe(path, st)
    nv, cls = read_cnf(path); ncl = length(cls)
    assigns = [BitVector(digits(m, base = 2, pad = nv)) for m in 0:(2^nv - 1)]
    satj(a, j) = all(c -> any(l -> (l > 0 ? a[abs(l)] : !a[abs(l)]), c), cls[1:j])
    semtri(U, Q, top) = (o = top - (2nv + 2); j = o < 2 ? 0 : min(ncl, (o - 2) ÷ 3 + 1);
        any(a -> satj(a, j) && haskey(U, pid(a, top, nv, cls)) && all(q -> pid(a, q.id.step, nv, cls) == q, Q), assigns))
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
                        sem = semtri(U, [x, y, w], top)
                        bump("fallos: cadena del estado unido por {x,y,w}: $(chain_through(g, [x, y, w], top))")
                        bump("fallos: trío {x,y,w} con solución $(sem ? "sí" : "no")")
                        println("FALLO $(basename(path)) cima=$top x=$(x.id) y=$(y.id) w=$(w.id) sem=$sem")
                        pat = String[]
                        for (who, ps) in (("ninguno", PathNodeId[]), ("x", [x]), ("y", [y]), ("w", [w]), ("x+y", [x, y]), ("x+w", [x, w]), ("y+w", [y, w]), ("x+y+w", [x, y, w]))
                            f = deepcopy(g)
                            redirect_stdout(devnull) do; isempty(ps) && (f.review_owners = true; GraphPath.make_review_owners!(f)); for p in ps; f.is_valid && GraphPath.filter!(f, SetNodesId([p.id])); end; end
                            f.is_valid && !isempty(ps) && bump("pin $who: estado válido, cadena por los nodos de mapa: $(chain_through_map(f, [p.id for p in ps], top))")
                            if !f.is_valid
                                bump("pin $who: estado muerto"); push!(pat, "muerto"); continue
                            end
                            V = tables(f); BV = bystep_of(V); Q = [x, y, w]
                            if !(all(q -> haskey(V, q), Q) && isclique(V, Q))
                                bump("pin $who: trío roto"); push!(pat, "roto"); continue
                            end
                            tp = all(l2 -> any(r -> owns(V, y, r) && owns(V, w, r) && ownsall(V, r, P) &&
                                         cxp(V, BV, P, y, r, top) && cxp(V, BV, P, w, r, top), get(BV, l2, PathNodeId[])), 0:top)
                            wit = all(l -> any(r -> ownsall(V, r, Q), get(BV, l, PathNodeId[])), 0:top)
                            bump("pin $who: trío vivo, testigos $(wit ? "sí" : "no"), TriP $(tp ? "ok" : "FALLA")")
                            push!(pat, wit ? "vivo+t" : "vivo")
                            wit && bump("pin $who: vivo con testigos, cadena por el trío: $(chain_through(f, Q, top))")
                        end
                        bump("patrón (x,y,w): $(join(pat, ", "))")
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
