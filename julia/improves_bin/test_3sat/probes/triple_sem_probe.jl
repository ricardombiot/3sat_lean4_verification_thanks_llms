# ¿Exactitud por tríos en el estado unido J? Toda clique de 3 nodos de J (y aparte, las que además tienen testigo en
# cada paso: r que posee a los tres) ¿tiene una asignación que cumple las cláusulas cerradas hasta la cima y pasa por
# los tres, S2 con su cima en J, S3 con todos sus nodos en J? docs/context/escalera_reader.md §4.2ξ.
#   julia --project=../.. triple_sem_probe.jl f1.cnf ...
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
            U = tables(g); ns = collect(keys(U))
            o = top - (2nv + 2); j = o < 2 ? 0 : min(ncl, (o - 2) ÷ 3 + 1)
            good = [a for a in assigns if satj(a, j)]
            paths = [[pid(a, l, nv, cls) for l in 0:top] for a in good]
            lv2 = BitVector([haskey(U, p[end]) for p in paths])
            lv3 = BitVector([all(q -> haskey(U, q), p) for p in paths])
            thru = Dict(x => BitVector([p[x.id.step + 1] == x for p in paths]) for x in ns)
            B = bystep_of(U)
            sns = sort(ns, by = x -> x.id.step)
            for i in eachindex(sns), k in i+1:length(sns)
                a = sns[i]; b = sns[k]
                (a.id.step != b.id.step && owns(U, a, b) && owns(U, b, a)) || continue
                ab = thru[a] .& thru[b]
                for m in k+1:length(sns)
                    c = sns[m]
                    (c.id.step != b.id.step && owns(U, a, c) && owns(U, c, a) && owns(U, b, c) && owns(U, c, b)) || continue
                    Q = [a, b, c]
                    wit = all(l -> any(r -> ownsall(U, r, Q), get(B, l, PathNodeId[])), 0:top)
                    abc = ab .& thru[c]
                    for (tag, on) in (("clique", true), ("clique con testigos", wit))
                        on || continue
                        bump("$tag: tríos")
                        any(abc .& lv2) ? bump("$tag: solución S2 ok") : bump("$tag: S2 FALLA")
                        if wit && !any(abc .& lv2) && tag != "clique"
                            inone = any(i -> isclique(Ts[i], Q), eachindex(Ts))
                            bump("  fallos con testigos: clique en alguna pieza $(inone ? "sí" : "no")")
                            println("EJ $(basename(path)) cima=$top Q=$([(q.id.step, q.id.index) for q in Q]) piezas=$(length(Ts))")
                        end
                        any(abc .& lv3) ? bump("$tag: solución S3 ok") : bump("$tag: S3 FALLA")
                    end
                end
            end
            bump("estados unidos")
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
