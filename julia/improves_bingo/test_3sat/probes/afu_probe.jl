# AF y crecimiento en la unión de una línea (inducción de LUA, docs/context/escalera_reader.md §4.2λ).
# U_S = unión de los estados de la línea n, cada uno filtrado por S (vacío o 2 de un nodo al azar).
#   AFU:  c :: Q0 buena en U_S con c en la cima n; c fija m (sus entradas del paso de m lo nombran) ⇒ buena en U_{S∪{m}}.
#   A1KU: Q buena en U_S sin miembro en la cima ⇒ ∃ c en la cima con c :: Q buena en U_S.
#   julia --project=../.. afu_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(41)
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
function filt(g, R)
    p = deepcopy(g)
    redirect_stdout(devnull) do; GraphPath.filter!(p, Set(R)); end
    p.is_valid ? tables(p) : nothing
end
function unionS(states, S)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for g in states
        T = filt(g, S); T === nothing && continue
        for (r, E) in T; union!(get!(U, r, Set{PathNodeId}()), E); end
    end
    U
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        states = Any[]
        CollectionTimeline.for_each_gpath(m.timeline, top, g -> g.is_valid && push!(states, deepcopy(g)))
        if length(states) >= 2
            ids = unique(vcat([[r.id for r in keys(tables(g))] for g in states]...))
            for S in vcat([NodeId[]], [[x] for x in rand(ids, min(2, length(ids)))])
                U = unionS(states, S); B = bystep_of(U); cache = Dict{NodeId, Any}()
                ns = collect(keys(U))
                # A1KU
                Qs = [[x] for x in ns if x.id.step < top]
                for i in eachindex(ns), k in i+1:length(ns)
                    (ns[i].id.step < top && ns[k].id.step < top && ns[i].id.step != ns[k].id.step && owns(U, ns[i], ns[k])) &&
                        push!(Qs, [ns[i], ns[k]])
                end
                for Q in Qs
                    good(U, B, Q, top) || continue
                    bump(any(c -> good(U, B, vcat([c], Q), top), get(B, top, PathNodeId[])) ? "A1KU ok" : "A1KU FALLA")
                end
                # AFU
                for c in get(B, top, PathNodeId[])
                    fixed = NodeId[]
                    for l in 0:top-1
                        il = unique([v.id for v in U[c] if v.id.step == l])
                        length(il) == 1 && push!(fixed, il[1])
                    end
                    for Q in vcat([[c]], [[c, q] for q in ns if q.id.step < top && owns(U, c, q)])
                        good(U, B, Q, top) || continue
                        for mid in fixed
                            r = get!(cache, mid) do
                                V = unionS(states, vcat(S, [mid])); (V, bystep_of(V))
                            end
                            ok = good(r[1], r[2], Q, top)
                            bump(ok ? "AFU ok" : "AFU FALLA")
                            ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("AFU: $(basename(path)) paso $top S=$S Q=$Q m=$mid"))
                        end
                    end
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
