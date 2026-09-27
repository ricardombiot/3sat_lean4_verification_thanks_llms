# M1bDeep (M1bDeep.lean): J estado unido de la línea n+1 (cima top = n+1), k clave de la fila n, i clave de la fila n-1.
# K2 = J|(R+k+i) válido ⇒ toda entrada (p, v) de K2 con p bajo la fila n-1 y v bajo la fila n es entrada de la pieza
# Q_{k,i} = upF W_i k (la pieza de la línea anterior que entró en la fuente X_k).
#   julia --project=../.. m1bdeep_probe.jl f1.cnf ...
include("./keytri_common.jl")
function up_pieces(m, gmap, s)
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
    pieces
end
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    prev = Dict{NodeId, Dict{NodeId, Any}}()
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = up_pieces(m, gmap, s)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step; n = top - 1
        if n >= 2
            CollectionTimeline.for_each_gpath(m.timeline, top, function (J)
                J.is_valid || return
                for R in sampleR(J)
                    G = pinned(J, R); G.is_valid || continue
                    UG = tables(G)
                    for k in unique(x.id for x in keys(UG) if x.id.step == n)
                        Qs = get(prev, k, nothing); Qs === nothing && continue
                        K = pinned(J, vcat(R, [k])); K.is_valid || continue
                        for i in unique(x.id for x in keys(tables(K)) if x.id.step == n - 1)
                            Q = get(Qs, i, nothing); Q === nothing && (bump("sin pieza Q"); continue)
                            K2 = pinned(J, vcat(R, [k, i])); K2.is_valid || continue
                            for (p, Tp) in tables(K2)
                                p.id.step < n - 1 || continue
                                for v in Tp
                                    v.id.step < n || continue
                                    ok = haskey(Q, p) && v in Q[p]
                                    bump("M1bDeep $(ok ? "ok" : "FALLA")")
                                    ok || ex("M1bDeep FALLA $(basename(path)) cima $top R=$R k=$k i=$i p=$(p.id) v=$(v.id)")
                                end
                            end
                        end
                    end
                end
            end)
        end
        prev = pieces
    end
end
run_all(probe)
