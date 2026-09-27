# M1 en partes (docs/context/ambfar.md §4.2ο.1). Estado unido J de la línea n+1 (cima n+1, claves en el paso n), piezas
# P_k = upF X_k d por clave k de la fuente. R válido en J (pins uno tras otro con su review):
#   M1a:        ∃ clave k (paso n) con J|(R+k) válido.
#   M1a-todas:  toda clave k de un nodo del paso n de J|R da J|(R+k) válido.
#   M1a-cima:   la clave de todo nodo de la cima de J|R da J|(R+k) válido.
#   M1b:        J|(R+k) válido ⇒ P_k|R válido.
#   M1b-entradas: J|(R+k) válido ⇒ toda entrada (r posee q) de J|(R+k) es entrada de P_k.
#   julia --project=../.. m1split_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(parse(Int, get(ENV, "SEED", "97")))
const NR = parse(Int, get(ENV, "NR", "10"))
mapids(g) = (S = Set{NodeId}(); for (_, line) in g.table_lines.table, (pid_, _) in line.table; push!(S, pid_.id); end; collect(S))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
function pinned(g, R)
    f = deepcopy(g)
    redirect_stdout(devnull) do
        f.review_owners = true; GraphPath.make_review_owners!(f)
        for r in R; f.is_valid && GraphPath.filter!(f, SetNodesId([r])); end
    end
    f
end
function sampleR(g)
    ids = mapids(g); bystep = Dict{Int, Vector{NodeId}}()
    for i in ids; push!(get!(bystep, i.step, NodeId[]), i); end
    Rs = Vector{Vector{NodeId}}([NodeId[]]); append!(Rs, [[i] for i in ids])
    for size in 2:3, _ in 1:NR
        ks = shuffle(collect(keys(bystep)))[1:min(size, length(bystep))]
        push!(Rs, [rand(bystep[s]) for s in ks])
    end
    Rs
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Dict{NodeId, Any}}()   # destino d => (clave de la fuente => pieza)
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && (get!(pieces, d, Dict{NodeId, Any}())[g.map_parent_id] = p)
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (J)
            J.is_valid || return
            Ps = get(pieces, J.map_parent_id, Dict{NodeId, Any}())
            isempty(Ps) && return
            tag = length(Ps) >= 2 ? "≥2" : "1"
            for R in sampleR(J)
                G = pinned(J, R)
                G.is_valid || continue
                UG = tables(G)
                keysn = unique([p.id for p in keys(UG) if p.id.step == top - 1])
                keystop = unique([p.parent_id for p in keys(UG) if p.id.step == top])
                val = Dict(k => pinned(J, vcat(R, [k])).is_valid for k in keysn)
                bump("M1a ($tag) $(any(values(val)) ? "ok" : "FALLA")")
                any(values(val)) || ex("M1a FALLA $(basename(path)) cima $top R=$R")
                bump("M1a-todas ($tag) $(all(values(val)) ? "ok" : "FALLA")")
                bump("M1a-cima ($tag) $(all(k -> get(val, k, false), keystop) ? "ok" : "FALLA")")
                for (k, ok) in val
                    ok || continue
                    haskey(Ps, k) || (bump("M1b clave sin pieza"); continue)
                    P = Ps[k]
                    pv = pinned(P, R).is_valid
                    bump("M1b ($tag) $(pv ? "ok" : "FALLA")")
                    pv || ex("M1b FALLA $(basename(path)) cima $top R=$R k=$k")
                    UK = tables(pinned(J, vcat(R, [k]))); UP = tables(P)
                    ent = all(((r, S),) -> haskey(UP, r) && all(q -> q in UP[r], S), UK)
                    bump("M1b-entradas ($tag) $(ent ? "ok" : "FALLA")")
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
