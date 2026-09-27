# ¿El pin del lector y su review arreglan los fallos de JoinChoiceP en el estado unido J? Para cada fallo (P = [x], enlace
# y–w, cliques de un nodo, exhaustivo) se fija en una copia de J el nodo de mapa de x, de y o de w (GraphPath.filter!,
# review con pair mode incluido) y se mira: estado muerto, trío {x, y, w} roto (algún nodo o par ya no está) o trío vivo;
# si sigue vivo, si TriP vale ya en el estado fijado. También fijando dos de los tres, uno tras otro, como el lector. docs/context/ambfar.md §4.2ξ.
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
                        bump("fallos: trío {x,y,w} con solución $(sem ? "sí" : "no")")
                        println("FALLO $(basename(path)) cima=$top x=$(x.id) y=$(y.id) w=$(w.id) sem=$sem")
                        pat = String[]
                        for (who, ps) in (("x", [x]), ("y", [y]), ("w", [w]), ("x+y", [x, y]), ("x+w", [x, w]), ("y+w", [y, w]), ("x+y+w", [x, y, w]))
                            f = deepcopy(g)
                            redirect_stdout(devnull) do; for p in ps; f.is_valid && GraphPath.filter!(f, SetNodesId([p.id])); end; end
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
