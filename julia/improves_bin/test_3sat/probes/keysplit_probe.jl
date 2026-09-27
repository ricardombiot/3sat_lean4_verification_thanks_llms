# KeySplit (KeyCone.lean): en J|R válido, para la clave k de un nodo vivo del paso top-1, con Π = P_k|R (la pieza de k
# fijada en R):
#   Π válido;  TriPin₁(Π, x);  CxPull: todo enlace y–w x-compatible de J|R (y, w poseen x) es x-compatible en Π.
#   julia --project=../.. keysplit_probe.jl f1.cnf ...
include("./keytri_common.jl")
include_string(Main, split(read("./keytri_probe.jl", String), "function probe")[1] |> s -> replace(s, "include(\"./keytri_common.jl\")" => ""))
cxT(U, x, y, w, top) = haskey(U, y) && haskey(U, w) && haskey(U, x) && w in U[y] &&
    all(l -> any(r -> r.id.step == l && r in U[w] && r in U[x], U[y]), 0:top)
function pull(UK, UP, x, top)
    for (y, Ty) in UK
        x in Ty || continue
        for w in Ty
            (haskey(UK, w) && x in UK[w] && cxT(UK, x, y, w, top)) || continue
            (haskey(UP, y) && x in UP[y] && haskey(UP, w) && x in UP[w] && cxT(UP, x, y, w, top)) || return false
        end
    end
    true
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
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && (get!(pieces, d, Dict{NodeId, Any}())[g.map_parent_id] = p)
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        top >= 2 || continue
        CollectionTimeline.for_each_gpath(m.timeline, top, function (J)
            J.is_valid || return
            Ps = get(pieces, J.map_parent_id, Dict{NodeId, Any}())
            for R in sampleR(J)
                G = pinned(J, R); G.is_valid || continue
                UK = tables(G)
                for k in unique([p.id for p in keys(UK) if p.id.step == top - 1])
                    haskey(Ps, k) || (bump("clave sin pieza"); continue)
                    Pi = pinned(Ps[k], R)
                    bump("Π válido $(Pi.is_valid ? "ok" : "FALLA")")
                    Pi.is_valid || continue
                    UP = tables(Pi)
                    xs = [x for x in keys(UK) if x.id == k]
                    t1 = [haskey(UP, x) && tripin1(UP, x, top) for x in xs]
                    pl = [haskey(UP, x) && pull(UK, UP, x, top) for x in xs]
                    bump("TriPin₁(Π, x) $(any(t1) ? "ok" : "FALLA")")
                    bump("CxPull $(any(pl) ? "ok" : "FALLA")")
                    both = any(t1 .& pl)
                    bump("KeySplit $(both ? "ok" : "FALLA")")
                    both || ex("KeySplit FALLA $(basename(path)) cima $top R=$R k=$k TriPin₁=$(t1) CxPull=$(pl)")
                end
            end
        end)
    end
end
run_all(probe)
