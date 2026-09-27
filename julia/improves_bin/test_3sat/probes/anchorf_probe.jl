# Pasos 1 y 2 hacia PieceLocalF, con filtros (docs/context/escalera_reader.md §4.2λ). Estado unido J de la línea n+1, piezas
# P_k, filtro R (vacío, de un nodo de mapa, o NR de 2–4 al azar); todo se mide en filterAll J R y filterAll P_k R.
#   A1 (anclar): Q buena en J sin miembro en la cima ⇒ ∃ w en la cima con Q ∪ {w} buena en J.
#   S2: Q buena en J con miembro w en la cima; P = pieza de clave w.parent_id (la única donde vive w):
#       ¿Q es clique en P? ¿en qué pasos falta testigo en P? Clasifica: ninguno / solo pasos de cláusula / otros (FALLA).
#   julia --project=../.. anchorf_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(19)
const NR = parse(Int, get(ENV, "NR", "4"))
function filt(g, R)
    p = deepcopy(g)
    redirect_stdout(devnull) do; GraphPath.filter!(p, Set(R)); end
    p.is_valid ? tables(p) : nothing
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
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function probe(path, st)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    kindof(l) = l == 0 ? "raíz" : l <= 2nv ? "var" : l == 2nv + 1 ? "mid" : "L$((l - (2nv + 2)) % 3 + 1)"
    isclause(l) = startswith(kindof(l), "L")
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
                p.is_valid && push!(get!(pieces, d, Any[]), (g.map_parent_id, p))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            ids = unique([r.id for r in keys(tables(g))])
            for R in vcat([NodeId[]], [[x] for x in ids], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
            U = filt(g, R); U === nothing && continue
            B = bystep_of(U)
            Tp = Dict{NodeId, Any}(); Bp = Dict{NodeId, Any}()
            for (k, p) in ps
                T = filt(p, R); T === nothing && continue
                Tp[k] = T; Bp[k] = bystep_of(T)
            end
            tops = get(B, top, PathNodeId[])
            ns = collect(keys(U)); Qs = [[x] for x in ns]
            for i in eachindex(ns), k in i+1:length(ns)
                ns[i].id.step == ns[k].id.step && continue
                owns(U, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
            end
            function s2(Q, w, tag)
                k = w.parent_id
                haskey(Tp, k) || (bump("$tag sin pieza"); return)
                T = Tp[k]; Bk = Bp[k]
                isclique(T, Q) || (bump("$tag no clique en P"); return)
                miss = [l for l in 0:top if !wit(T, Bk, Q, l)]
                if isempty(miss); bump("$tag P buena")
                elseif all(isclause, miss); bump("$tag faltan solo cláusula")
                else
                    bump("$tag FALLA (falta paso no cláusula)")
                    get(st, "ej", 0) < 5 && (bump("ej"); println("$tag: $(basename(path)) paso $top R=$R Q=$Q faltan $(map(l -> "$l($(kindof(l)))", miss))"))
                end
            end
            for Q in Qs
                good(U, B, Q, top) || continue
                iw = findfirst(q -> q.id.step == top, Q)
                if iw === nothing
                    ext = [w for w in tops if good(U, B, vcat(Q, [w]), top)]
                    bump(isempty(ext) ? "A1 FALLA" : "A1 ok")
                    for w in ext; s2(vcat(Q, [w]), w, "S2 anclada"); end
                else
                    s2(Q, Q[iw], "S2")
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
