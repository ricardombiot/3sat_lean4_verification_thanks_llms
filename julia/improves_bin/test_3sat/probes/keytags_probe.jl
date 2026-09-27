# Exactitud de la etiqueta de clave (informe v196 §3, KEY_MODE = :on): en cada estado unido J de la línea n+1, para
# toda entrada (p, v) de un nodo p por debajo de la fila de claves y toda clave k con pieza P_k:
#   k ∈ etiqueta(p, v)  ⇔  v ∈ T_{P_k}(p).
# Y, con las dos reglas, M1b-entradas por construcción: J|(R+k) válido ⇒ toda entrada de las filas de abajo es de P_k.
#   julia --project=../.. keytags_probe.jl f1.cnf ...
include("./keytri_common.jl")
GraphPath.KEY_MODE[] = :on
GraphPath.KEYCHECK_MODE[] = Symbol(get(ENV, "KEYCHECK", "on"))
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
            kt = J.key_tags
            if kt === nothing
                bump("J sin etiquetas"); return
            end
            UJ = tables(J)
            tag(p, v) = kt.single !== nothing ? SetNodesId([kt.single]) : get(kt.tags, (p, v), SetNodesId())
            for (p, Tp) in UJ
                p.id.step < kt.key_step || continue
                for v in Tp, (k, UP) in Ps
                    a = k in tag(p, v); b = haskey(UP, p) && v in UP[p]
                    bump("etiqueta exacta $(a == b ? "ok" : (a ? "FALLA (sobra)" : "FALLA (falta)"))")
                    a == b || ex("FALLA $(basename(path)) cima $top p=$p v=$v k=$k etiqueta=$a pieza=$b")
                end
            end
            # M1b-entradas por construcción
            for R in sampleR(J), k in keys(Ps)
                G = pinned(J, vcat(R, [k])); G.is_valid || continue
                UP = Ps[k]
                ok = all(((r, S),) -> r.id.step >= kt.key_step || (haskey(UP, r) && all(q -> q in UP[r], S)), tables(G))
                bump("M1b-entradas $(ok ? "ok" : "FALLA")")
            end
        end)
    end
end
run_all(probe)
