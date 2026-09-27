# KFix (M1bOwn.lean, §4.2ο.2): en J|R válido y para cada clave k, el mayor conjunto S_k de enlaces (a, b) (b ∈ T(a),
# a y b vivos, a = b incluido) cerrado para k: en cada paso l hay r con (a, r), (b, r) ∈ S_k y r posee un nodo de k.
# KFix: todo (p, v) ∈ S_k con p por debajo de la fila de claves tiene v ∈ T_{P_k}(p). Con k fijada, todos los enlaces
# forman un conjunto cerrado, así que KFix da M1bLowOwn. KTriK es la primera ronda del cierre (medida falsa).
#   julia --project=../.. kfix_probe.jl f1.cnf ...
include("./keytri_common.jl")
function gfp(U, kof, k, top)
    S = Set{Tuple{PathNodeId, PathNodeId}}()
    for (a, Ta) in U, b in Ta; haskey(U, b) && push!(S, (a, b)); end
    nb = Dict{PathNodeId, Set{PathNodeId}}()
    for (a, b) in S; push!(get!(nb, a, Set{PathNodeId}()), b); end
    changed = true
    while changed
        changed = false
        bad = Tuple{PathNodeId, PathNodeId}[]
        for (a, b) in S
            na = get(nb, a, Set{PathNodeId}()); nbb = get(nb, b, Set{PathNodeId}())
            ok = all(l -> any(r -> r.id.step == l && r in nbb && k in kof[r], na), 0:top)
            ok || push!(bad, (a, b))
        end
        for (a, b) in bad; delete!(S, (a, b)); delete!(nb[a], b); changed = true; end
    end
    S
end
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Dict{NodeId, Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                q = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(q, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                q.is_valid && (get!(pieces, d, Dict{NodeId, Any}())[g.map_parent_id] = tables(q))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        top >= 2 || continue
        CollectionTimeline.for_each_gpath(m.timeline, top, function (J)
            J.is_valid || return
            Ps = get(pieces, J.map_parent_id, Dict{NodeId, Any}())
            isempty(Ps) && return
            for R in sampleR(J)
                G = pinned(J, R); G.is_valid || continue
                U = tables(G)
                tag = isempty(R) ? "R=∅" : "R≠∅"
                kof = Dict(r => Set(x.id for x in T if x.id.step == top - 1) for (r, T) in U)
                for k in unique(x.id for x in keys(U) if x.id.step == top - 1)
                    UP = get(Ps, k, nothing); UP === nothing && continue
                    S = gfp(U, kof, k, top)
                    fails = [(p, v) for (p, v) in S if p.id.step < top - 1 && !(haskey(UP, p) && v in UP[p])]
                    bump("KFix ($tag) $(isempty(fails) ? "ok" : "FALLA")")
                    isempty(fails) || ex("KFix FALLA $(basename(path)) cima $top R=$R k=$k: $(length(fails)) enlaces, p.id=$(fails[1][1].id) v.id=$(fails[1][2].id)")
                    st["KFix enlaces comprobados"] = get(st, "KFix enlaces comprobados", 0) + count(((p, _),) -> p.id.step < top - 1, S)
                end
            end
        end)
    end
end
bumpn!(st, k, n) = (st[k] = get(st, k, 0) + n)
run_all(probe)
