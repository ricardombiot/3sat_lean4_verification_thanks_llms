# LUA en la forma exacta de AnchorPiece.topPieceF_of_lua. Estado unido J (línea n+1, clave d), filtro R (vacío, de un
# nodo, NR de 2–4 al azar). K = filterAll J R sin su cima. c en el paso n (cima de K), Q = c o c+q:
#   LUA: Q buena en K ⇒ Q buena en filterAll X_c (reqs(d) ++ R≤n), con X_c la fuente de clave c.id (y válido).
#   julia --project=../.. luaj_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(23)
const NR = parse(Int, get(ENV, "NR", "4"))
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
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        srcs = Dict{NodeId, Any}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid && (srcs[g.map_parent_id] = deepcopy(g))
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        CollectionTimeline.for_each_gpath(m.timeline, s + 1, function (g)
            g.is_valid || return
            reqs = collect(SatMachine.map_get_node(gmap, g.map_parent_id).requires)
            ids = unique([r.id for r in keys(tables(g))])
            for R in vcat([NodeId[]], [[x] for x in ids], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
                F = filt(g, R); F === nothing && continue
                K = Dict(r => Set(v for v in S if v.id.step <= s) for (r, S) in F if r.id.step <= s)
                B = bystep_of(K)
                Rlow = [x for x in R if x.step <= s]
                cache = Dict{NodeId, Any}()
                for c in get(B, s, PathNodeId[])
                    haskey(srcs, c.id) || (bump("LUA sin fuente"); continue)
                    G = get!(cache, c.id) do
                        T = filt(srcs[c.id], vcat(reqs, Rlow)); T === nothing ? nothing : (T, bystep_of(T))
                    end
                    for Q in vcat([[c]], [[c, q] for q in keys(K) if q.id.step < s && owns(K, c, q)])
                        good(K, B, Q, s) || continue
                        ok = G !== nothing && good(G[1], G[2], Q, s)
                        bump(ok ? "LUA ok" : "LUA FALLA")
                        ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("LUA: $(basename(path)) paso $(s+1) R=$R Q=$Q"))
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
