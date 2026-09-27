# Selección de miembro en GLF* (lean/improves_bin, paso 3). Familia: estados de una línea, cada uno con pins al azar
# (se repiten). Para cliques Q con testigos en la unión y una clave de cima m que poseen todos los testigos
# (restricción R = [m]), o un miembro de Q en la cima (m = su id):
#   WL: cada testigo que posee un nodo de la cima con id m posee Q dentro de los miembros de clave m
#   WL1: en cada paso hay algún testigo que posee Q dentro de los miembros de clave m
#   CL: Q es clique dentro de los miembros de clave m
# (b) CH: toda cadena de la unión (búsqueda acotada) es cadena de algún miembro.
#   julia --project=../.. select_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
function nodes(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; D[pid] = node; end
    D
end
tab(n) = (S = Set{PathNodeId}(); for (_, set) in n.owners.table; union!(S, set); end; S)
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
function uni(Ts)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for T in Ts; for (r, S) in T; union!(get!(U, r, Set{PathNodeId}()), S); end; end
    U
end
function filt(g, pins)
    f = deepcopy(g); redirect_stdout(devnull) do; GraphPath.filter!(f, Set(pins)); end; f
end
randpins(rng, gmap, s) = s <= 0 ? NodeId[] : [rand(rng, collect(GraphMapBin.get_ids_step(gmap, Step(t)))) for t in rand(rng, 0:s-1, rand(rng, 0:2))]
function chains(D, top, cap)
    out = Vector{Vector{PathNodeId}}()
    function go(p)
        length(out) >= cap && return
        last = p[end]
        if last.id.step == 0; push!(out, copy(p)); return; end
        for c in D[last].parents
            haskey(D, c) || continue
            all(a -> (c in tab(D[a])) && (a in tab(D[c])), p) || continue
            push!(p, c); go(p); pop!(p)
        end
    end
    for t in [p for p in keys(D) if p.id.step == top]; go([t]); end
    out
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    rng = MersenneTwister(5)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        states = Any[]
        CollectionTimeline.for_each_gpath(m.timeline, s, g -> (g.is_valid && push!(states, g)))
        length(Set(g.map_parent_id for g in states)) >= 2 && for _ in 1:3
            fam = [(g.map_parent_id, filt(g, randpins(rng, gmap, s))) for g in states for _ in 1:2]
            fam = [(k, f) for (k, f) in fam if f.is_valid]
            length(Set(first.(fam))) >= 2 || continue
            Ds = [nodes(f) for (_, f) in fam]; Ts = [Dict(r => tab(n) for (r, n) in D) for D in Ds]
            U = uni(Ts); top = s
            B = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(B, r.id.step, PathNodeId[]), r); end
            keys_ = unique(first.(fam))
            Um = Dict(k => uni([Ts[i] for i in eachindex(fam) if fam[i][1] == k]) for k in keys_)
            ns = collect(keys(U)); Qs = [[x] for x in ns]
            for i in eachindex(ns), j in i+1:length(ns)
                ns[i].id.step == ns[j].id.step && continue
                owns(U, ns[i], ns[j]) && push!(Qs, [ns[i], ns[j]])
            end
            for Q in Qs
                isclique(U, Q) || continue
                for k in keys_
                    topk = [t for t in get(B, top, PathNodeId[]) if t.id == k]
                    ownsk(r) = any(t -> owns(U, r, t), topk)
                    wits(l) = [r for r in get(B, l, PathNodeId[]) if all(q -> owns(U, r, q), Q) && ownsk(r)]
                    hasTop = any(q -> q.id.step == top && q.id == k, Q)
                    all(l -> !isempty(wits(l)), 0:top) || continue
                    bump("Q con testigos que poseen la cima $(hasTop ? "(miembro en la cima)" : "(restricción R)")")
                    V = Um[k]
                    bump(all(l -> all(r -> all(q -> owns(V, r, q), Q), wits(l)), 0:top) ? "  WL ok" : "  WL FALLA")
                    bump(all(l -> any(r -> all(q -> owns(V, r, q), Q), wits(l)), 0:top) ? "  WL1 ok" : "  WL1 FALLA")
                    bump(isclique(V, Q) ? "  CL ok" : "  CL FALLA")
                end
            end
            # (b)
            Dall = Dict{PathNodeId, Any}()
            for D in Ds, (r, n) in D
                if haskey(Dall, r)
                    Dall[r] = (parents = union(Dall[r].parents, n.parents), owners = nothing)
                else
                    Dall[r] = (parents = Set(n.parents), owners = nothing)
                end
            end
            DU = Dict(r => (parents = Dall[r].parents, T = U[r]) for r in keys(Dall))
            out = Vector{Vector{PathNodeId}}()
            function go(p)
                length(out) >= 300 && return
                last = p[end]
                if last.id.step == 0; push!(out, copy(p)); return; end
                for c in DU[last].parents
                    haskey(DU, c) || continue
                    all(a -> (c in DU[a].T) && (a in DU[c].T), p) || continue
                    push!(p, c); go(p); pop!(p)
                end
            end
            for t in get(B, top, PathNodeId[]); go([t]); end
            for ch in out
                inm = any(i -> all(a -> haskey(Ds[i], a) && all(b -> b in Ts[i][a], ch) &&
                    all(k -> k == length(ch) || ch[k+1] in Ds[i][a].parents, [findfirst(==(a), ch)]), ch), eachindex(fam))
                bump(inm ? "CH ok: la cadena de la unión es de un miembro" : "CH FALLA")
            end
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
