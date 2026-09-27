# KTri (para M1bLowOwn, M1Parts.lean): en J|R válido (J estado unido, cima top, claves en top-1), si p (paso < top-1) y v (cualquier paso)
# se poseen y los dos poseen un nodo x del paso top-1 (clave k = x.id), entonces v está en la tabla de p en la
# pieza P_k. Con R = k::R' da M1bLowOwn (en el paso top-1 de J|(k::R') solo vive k).
#   KTri:     la implicación, para todo x común.
#   KTri-nodo: p es nodo de P_k (sale de la fila pura de x).
#   KTriK: si en cada paso l hay un testigo común r ∈ T(p) ∩ T(v) que posee un nodo de la clave k, entonces v ∈ T_{P_k}(p).
#     Con k fijada todo testigo lo cumple, así que KTriK da M1bLowOwn sin pedir nada del review.
#   julia --project=../.. ktri_probe.jl f1.cnf ...
include("./keytri_common.jl")
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
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && (get!(pieces, d, Dict{NodeId, Any}())[g.map_parent_id] = tables(p))
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
                xs = [x for x in keys(U) if x.id.step == top - 1]
                kof = Dict(r => Set(x.id for x in T if x.id.step == top - 1) for (r, T) in U)
                for (p, Tp) in U
                    p.id.step < top - 1 || continue
                    for v in Tp
                        haskey(U, v) || continue
                        com = [r for r in Tp if r in U[v] && haskey(kof, r)]
                        Ks = nothing
                        for l in 0:top
                            S = Set{NodeId}()
                            for r in com; r.id.step == l && union!(S, kof[r]); end
                            Ks = Ks === nothing ? S : intersect(Ks, S)
                        end
                        for k in Ks
                            UP = get(Ps, k, nothing)
                            UP === nothing && (bump("KTriK clave sin pieza"); continue)
                            okK = haskey(UP, p) && v in UP[p]
                            bump("KTriK ($tag) $(okK ? "ok" : "FALLA")")
                            okK || ex("KTriK FALLA $(basename(path)) cima $top R=$R p=$p v=$v k=$k")
                        end
                        for x in xs
                            (x in Tp && x in U[v]) || continue
                            UP = get(Ps, x.id, nothing)
                            UP === nothing && (bump("KTri clave sin pieza"); continue)
                            bump("KTri-nodo ($tag) $(haskey(UP, p) ? "ok" : "FALLA")")
                            ok = haskey(UP, p) && v in UP[p]
                            bump("KTri ($tag) $(ok ? "ok" : "FALLA")")
                        end
                    end
                end
            end
        end)
    end
end
run_all(probe)
