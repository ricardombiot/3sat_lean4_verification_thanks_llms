# La inducción de LUA sobre la unión de una línea como estado (docs/context/ambfar.md §4.2λ).
# U = unión (join) de todos los estados de la línea n; FU = filterAll U S (S vacío o 2 de un nodo al azar).
#   LUAU:  c :: Q0 buena en FU con c en la cima n ⇒ buena en filterAll X_c S (X_c: estado de clave c.id).
#   AFU':  c :: Q0 buena en FU, c fija m ⇒ buena en filterAll U (S ∪ {m}).
#   TMU:   c :: Q0 buena en FU, c con dos padres ⇒ ∃ padre p con p :: Q0 buena en FU.
#   A1KU': Q buena en FU sin miembro en la cima ⇒ ∃ c en la cima con c :: Q buena en FU.
#   julia --project=../.. luau_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(43)
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}(); P = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
        P[pid_] = Set(node.parents)
    end
    U, P
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function filtG(g, R)
    p = deepcopy(g)
    redirect_stdout(devnull) do; GraphPath.filter!(p, Set(R)); end
    p.is_valid ? p : nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        states = Dict{NodeId, Any}()
        CollectionTimeline.for_each_gpath(m.timeline, top, g -> g.is_valid && (states[g.map_parent_id] = deepcopy(g)))
        if length(states) >= 2
            ks = collect(keys(states))
            U0 = deepcopy(states[ks[1]])
            for k in ks[2:end]
                o = deepcopy(states[k]); o.map_parent_id = U0.map_parent_id
                GraphPath.do_join!(U0, o)
            end
            ids = unique([r.id for r in keys(tables(U0)[1])])
            for S in vcat([NodeId[]], [[x] for x in rand(ids, min(2, length(ids)))])
                FUg = filtG(U0, S); FUg === nothing && continue
                FU, Par = tables(FUg); B = bystep_of(FU); ns = collect(keys(FU))
                cacheX = Dict{NodeId, Any}(); cacheU = Dict{NodeId, Any}()
                Xc(k) = get!(cacheX, k) do
                    haskey(states, k) || return nothing
                    g = filtG(states[k], S); g === nothing ? nothing : (T = tables(g)[1]; (T, bystep_of(T)))
                end
                for c in get(B, top, PathNodeId[])
                    fixed = NodeId[]
                    for l in 0:top-1
                        il = unique([v.id for v in FU[c] if v.id.step == l])
                        length(il) == 1 && push!(fixed, il[1])
                    end
                    pars = collect(get(Par, c, Set()))
                    for Q in vcat([[c]], [[c, q] for q in ns if q.id.step < top && owns(FU, c, q)])
                        good(FU, B, Q, top) || continue
                        X = Xc(c.id)
                        ok = X !== nothing && good(X[1], X[2], Q, top)
                        bump(ok ? "LUAU ok" : "LUAU FALLA")
                        ok || get(st, "ej", 0) >= 4 || (bump("ej"); println("LUAU: $(basename(path)) paso $top S=$S Q=$Q"))
                        for mid in fixed
                            r = get!(cacheU, mid) do
                                g = filtG(U0, vcat(S, [mid])); g === nothing ? nothing : (T = tables(g)[1]; (T, bystep_of(T)))
                            end
                            bump(r !== nothing && good(r[1], r[2], Q, top) ? "AFU' ok" : "AFU' FALLA")
                        end
                        if length(pars) >= 2
                            Q0 = [q for q in Q if q != c]
                            bump(any(p -> good(FU, B, vcat([p], Q0), top), pars) ? "TMU ok" : "TMU FALLA")
                        end
                    end
                end
                Qs = [[x] for x in ns if x.id.step < top]
                for i in eachindex(ns), k in i+1:length(ns)
                    (ns[i].id.step < top && ns[k].id.step < top && ns[i].id.step != ns[k].id.step && owns(FU, ns[i], ns[k])) &&
                        push!(Qs, [ns[i], ns[k]])
                end
                for Q in Qs
                    good(FU, B, Q, top) || continue
                    bump(any(c -> good(FU, B, vcat([c], Q), top), get(B, top, PathNodeId[])) ? "A1KU' ok" : "A1KU' FALLA")
                end
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
