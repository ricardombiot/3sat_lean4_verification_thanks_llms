# Exactitud de las etiquetas de todos los niveles (informe v197 §5, KEYTAGS_MODE = :on), en cada estado unido J de la
# línea n+1 (cima n+1):
#   fila n   (la del último join): k ∈ tag_n(p, v)  ⇔  v ∈ T_{P_k}(p), para P_k la pieza de J con clave k;
#   fila n-1 (heredada):           j ∈ tag_{n-1}(p, v) ⇒ ∃ k con v ∈ T_{P_k}(p) y v ∈ T_{Q_{k,j}}(p), para Q_{k,j} la
#                                  pieza de la línea anterior (fuente con clave j) que entró en la fuente X_k de P_k.
#                                  Solo entradas con p y v hasta el paso n (los nodos de la cima n+1 no existían en Q).
#   M1b-entradas: J fijado (con etiquetas) en R + k válido ⇒ toda entrada de las filas bajo n es de P_k.
#   julia --project=../.. keytags_all_probe.jl f1.cnf ...
include("./keytri_common.jl")
GraphPath.KEYTAGS_MODE[] = :on

function up_pieces(m, gmap, s)
    pieces = Dict{NodeId, Dict{NodeId, Any}}()        # destino => (clave de la fuente => tablas de la pieza)
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
        top = m.current_step
        n = top - 1
        if top >= 2
            CollectionTimeline.for_each_gpath(m.timeline, top, function (J)
                J.is_valid || return
                t = J.key_tags
                t === nothing && (bump("J sin etiquetas"); return)
                Ps = get(pieces, J.map_parent_id, Dict{NodeId, Any}())
                UJ = tables(J)
                for (p, Tp) in UJ, v in Tp
                    e = (p, v)
                    # fila n
                    mk = GraphPath.tag_mask(t, e, n)
                    if mk === nothing
                        bump("fila n sin máscara")
                    else
                        for (k, UP) in Ps
                            a = (mk & GraphPath.key_bit(k)) != 0; b = haskey(UP, p) && v in UP[p]
                            bump("fila n exacta $(a == b ? "ok" : (a ? "FALLA (sobra)" : "FALLA (falta)"))")
                            a == b || ex("fila n FALLA $(basename(path)) cima $top p=$p v=$v k=$k etiqueta=$a pieza=$b")
                        end
                    end
                    # fila n-1
                    (n >= 1 && p.id.step <= n) || continue
                    # un owner de la cima (paso n+1) no existía en Q: su máscara la hereda del padre, no se compara
                    v.id.step <= n || (bump("fila n-1: owner en la cima (heredada)"); continue)
                    mj = GraphPath.tag_mask(t, e, n - 1)
                    mj === nothing && (bump("fila n-1 sin máscara"); continue)
                    for bitj in 0:63
                        (mj >> bitj) & 1 == 1 || continue
                        j = (step = n - 1, index = bitj)
                        ok = any(((k, UP),) -> haskey(UP, p) && v in UP[p] &&
                                 (Q = get(get(prev, k, Dict{NodeId, Any}()), j, nothing); Q !== nothing && haskey(Q, p) && v in Q[p]), Ps)
                        bump("fila n-1 ⇒ $(ok ? "ok" : "FALLA")")
                        ok || ex("fila n-1 FALLA $(basename(path)) cima $top p=$p v=$v j=$j")
                    end
                end
                # M1b-entradas por construcción
                for R in sampleR(J), k in keys(Ps)
                    G = pinned(J, vcat(R, [k])); G.is_valid || continue
                    UP = Ps[k]
                    ok = all(((r, S),) -> r.id.step >= n || (haskey(UP, r) && all(q -> q in UP[r], S)), tables(G))
                    bump("M1b-entradas $(ok ? "ok" : "FALLA")")
                end
            end)
        end
        prev = pieces
    end
end
run_all(probe)
