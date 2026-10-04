# ULUA (LUA sin ancla). Estado unido J (línea n+1, clave d), filtro R (vacío, de un nodo, NR de 2–4 al azar).
# K = filterAll J R sin su cima. Q (1 o 2 nodos, todos por debajo de n+1, sin exigir miembro en el paso n):
#   ULUA: Q buena en K ⇒ ∃ fuente X_i (enviada a d) con Q buena en filterAll X_i (pinsW_i ++ R≤n), donde pinsW_i son los
#         requisitos de d más L1 = 1 si esa fuente salta la ventana (clave (n,0), d = (n+1,0) en un L3).
#   Reglas locales para elegir la fuente (sondeo rápido: filtro vacío, 3 de un nodo, NR de 2–4):
#   A1K: ∃ c en el paso n de K con Q ∪ {c} buena en K (crecer en la cima de K).
#   R1∀: la fuente de TODO testigo de Q en el paso n sirve.   R1∃: la de ALGUNO sirve.
#   julia --project=../.. ulua_rules_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(37)
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
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    isL3(l) = l >= 2nv + 2 && (l - (2nv + 2)) % 3 == 2
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
            for R in vcat([NodeId[]], [[x] for x in (isempty(ids) ? ids : rand(ids, min(3, length(ids))))], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
                F = filt(g, R); F === nothing && continue
                K = Dict(r => Set(v for v in S if v.id.step <= s) for (r, S) in F if r.id.step <= s)
                B = bystep_of(K)
                Rlow = [x for x in R if x.step <= s]
                cache = Dict{NodeId, Any}()
                srcs_d = [k for k in keys(srcs) if g.map_parent_id in SatMachine.map_get_node(gmap, k).sons]
                function G(k)
                    get!(cache, k) do
                        pins = vcat(reqs, Rlow)
                        (k.index == 0 && g.map_parent_id.index == 0 && isL3(s + 1)) && push!(pins, (step = s - 1, index = 1))
                        T = filt(srcs[k], pins); T === nothing ? nothing : (T, bystep_of(T))
                    end
                end
                ns = collect(keys(K)); Qs = [[x] for x in ns]
                for i in eachindex(ns), k in i+1:length(ns)
                    ns[i].id.step == ns[k].id.step && continue
                    owns(K, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
                end
                okG(k, Q) = haskey(srcs, k) && k in srcs_d && (r = G(k); r !== nothing && good(r[1], r[2], Q, s))
                for Q in Qs
                    good(K, B, Q, s) || continue
                    any(q -> q.id.step == s, Q) && continue
                    bump("Q sin miembro en n")
                    wits = [r for r in get(B, s, PathNodeId[]) if all(q -> owns(K, r, q), Q)]
                    bump(any(c -> good(K, B, vcat(Q, [c]), s), get(B, s, PathNodeId[])) ? "A1K ok" : "A1K FALLA")
                    bump(all(r -> okG(r.id, Q), wits) ? "R1∀ ok" : "R1∀ FALLA")
                    bump(any(r -> okG(r.id, Q), wits) ? "R1∃ ok" : "R1∃ FALLA")
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
