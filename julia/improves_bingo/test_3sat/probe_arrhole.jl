# ArrHole sin contexto (29-sept-2026, rama reader-stuck; sonda rápida).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_arrhole.jl <salida.tsv>
#
# Para cada llegada X (remitente S del nivel k, destino D) y cada arista y–w de S con y, w vivos en X que X no tiene:
#   hole: hay un paso l en el que ningún vivo de X es vecino común de y y w con las aristas de las entradas del nivel k.
#   holeS: lo mismo con las aristas de S (G1). holeArr: con las aristas de las llegadas a D (ArrivalGap).

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const SENDER = Dict{Any, Any}()
const ARR = Dict{Any, Any}()
const REQS = Dict{Any, Any}()


Core.eval(PathOwnersGraph, quote
    const LOGHOOK = Ref{Any}(nothing)
    function remove_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId; rule :: Symbol)
        x == w && return false
        k = edge_key(x, w)
        haskey(g.edges, k) || return false
        e = g.edges[k]
        delete!(g.edges, k)
        dx = _drop!(g.inc[x], w)
        dw = _drop!(g.inc[w], x)
        Undo.active() && Undo.record!(function ()
            g.edges[k] = e
            dx && push!(g.inc[x][step_of(w)], w)
            dw && push!(g.inc[w][step_of(x)], x)
        end)
        REMOVED_BY[rule] = get(REMOVED_BY, rule, 0) + 1
        LOGHOOK[] === nothing || LOGHOOK[](x, w, rule)
        return true
    end
end)
const REMOVALS = Dict{Any, Any}()
const TRIGS = Dict{Any, Any}()
const CURTRIG = Ref{Any}(nothing)
const REQS = Dict{Any, Any}()
Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        key = (gpath.map_parent_id, Int(gpath.current_step))
        haskey($(SENDER), key) || ($(SENDER)[key] = deepcopy(gpath))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        trig = Dict{Any, Any}()
        $(CURTRIG)[] = trig
        $(TRIGS)[(map_id_node, gpath.map_parent_id, Int(gpath.current_step))] = trig
        $(REQS)[(map_id_node, gpath.map_parent_id, Int(gpath.current_step))] = copy(requires)
        log = Dict{Any, Symbol}()
        PathOwnersGraph.LOGHOOK[] = (x, w, r) -> (log[Set([x, w])] = r)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        PathOwnersGraph.LOGHOOK[] = nothing
        $(CURTRIG)[] = nothing
        $(REMOVALS)[(map_id_node, key[1], key[2])] = log
        $(ARR)[(map_id_node, key[1], key[2])] = deepcopy(gpath)
        $(REQS)[(map_id_node, key[1], key[2])] = copy(requires)
    end
end)

alive(h) = [x for (_, xs) in h.og.alive for x in xs]
tops(h) = collect(get(h.og.alive, Int(h.current_step) - 1, SetPathNodesId()))
function groups_of(h)
    gr = Dict{Any, Vector{PathNodeId}}()
    for q in tops(h)
        push!(get!(gr, (q.id, q.parent_id), PathNodeId[]), q)
    end
    return gr
end
star(h, Q) = Set(z for z in alive(h) if any(q -> PG.has_edge(h.og, z, q), Q))



function on_pair_bad(og, a, b)
    T = CURTRIG[]; T === nothing && return
    haskey(T, Set([a, b])) && return
    st = Int[]
    for (l, zs) in og.alive
        any(z -> PG.has_edge(og, a, z) && PG.has_edge(og, b, z), zs) || push!(st, Int(l))
    end
    T[Set([a, b])] = st
end

function judge_arr(bystep)
    for ((D, sk, k), X) in ARR
        X.is_valid || continue
        es = get(bystep, k, nothing); es === nothing && continue
        S = get(es, sk, nothing); S === nothing && continue
        AX = alive(X)
        ogsK = [E.og for E in values(es)]
        adjK(a, b) = a == b || any(o -> PG.has_edge(o, a, b), ogsK)
        arrD = [Y.og for ((D2, _, k2), Y) in ARR if D2 == D && k2 == k && Y.is_valid]
        adjD(a, b) = a == b || any(o -> PG.has_edge(o, a, b), arrD)
        # parejas ausentes: y–w de otra entrada del nivel k, no de S, con y, w vivos en X
        for E in values(es)
            E === S && continue
            for (y, w) in keys(E.og.edges)
                (y == w || PG.has_edge(S.og, y, w) || !PG.is_alive(X.og, y) || !PG.is_alive(X.og, w)) && continue
                bump(:abs)
                PG.has_edge(X.og, y, w) && (bump(:abs_inX); continue)
                hh = any(0:k-1) do l
                    all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), AX)
                end
                hh && bump(:abs_hole)
                topsX = [q for q in AX if Int(q.id.step) == Int(X.current_step) - 1]
                if any(q -> PG.has_edge(X.og, y, q) && PG.has_edge(X.og, w, q), topsX)
                    bump(:abs_ctop); hh && bump(:abs_ctop_hole)
                end
            end
        end
        # ausentes con la arista en otra entrada del nivel SIGUIENTE (no en la de D)
        nx = get(bystep, k + 1, nothing)
        if nx !== nothing
            for (key2, B) in nx
                key2 == D && continue
                AD = get(nx, D, nothing)
                for (y, w) in keys(B.og.edges)
                    (y == w || PG.has_edge(S.og, y, w) || !PG.is_alive(X.og, y) || !PG.is_alive(X.og, w)) && continue
                    (AD !== nothing && PG.has_edge(AD.og, y, w)) && continue
                    bump(:ab1)
                    hh = any(0:k-1) do l
                        all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), AX)
                    end
                    hh && bump(:ab1_hole)
                    topsX = [q for q in AX if Int(q.id.step) == Int(X.current_step) - 1]
                    if any(q -> PG.has_edge(X.og, y, q) && PG.has_edge(X.og, w, q), topsX)
                        bump(:ab1_ctop); hh && bump(:ab1_ctop_hole)
                    end
                    if any(q -> PG.has_edge(X.og, y, q), topsX) && any(q -> PG.has_edge(X.og, w, q), topsX)
                        bump(:ab1_star); hh && bump(:ab1_star_hole)
                    end
                end
            end
        end
        for (y, w) in keys(S.og.edges)
            (y == w || !PG.is_alive(X.og, y) || !PG.is_alive(X.og, w) || PG.has_edge(X.og, y, w)) && continue
            bump(:np)
            rl = get(get(REMOVALS, (D, sk, k), Dict()), Set([y, w]), :none)
            # apoyo de la pareja añadida en X: padres/hijos de y poseídos por w y al revés
            function supp(a, b)
                nd = PathCollectionLines.get_node(X.table_lines, a)
                nd === nothing && return false
                okp = Int(a.id.step) < 1 || any(p -> PG.has_edge(X.og, a, p) && PG.has_edge(X.og, p, b), nd.parents)
                oks = Int(a.id.step) + 1 >= Int(X.current_step) || any(q -> PG.has_edge(X.og, a, q) && PG.has_edge(X.og, q, b), nd.sons)
                okp && oks
            end
            (supp(y, w) && supp(w, y)) ? bump(:supp_ok) : bump(:supp_fail)
            # la cadena de padres de y: fronteras (no poseen a w, algún padre sí)
            parsX(a) = (nd = PathCollectionLines.get_node(X.table_lines, a);
                        nd === nothing ? PathNodeId[] : [p for p in nd.parents if PG.has_edge(X.og, a, p)])
            holesX(a, b) = [l for l in 0:k if l != Int(a.id.step) && l != Int(b.id.step) &&
                            all(r -> Int(r.id.step) != l || !(PG.has_edge(X.og, a, r) && PG.has_edge(X.og, b, r)), AX)]
            seen = Set{PathNodeId}([y]); todo = [y]; bnd = PathNodeId[]; reach = false
            while !isempty(todo)
                a = pop!(todo)
                ps = parsX(a)
                if any(p -> PG.has_edge(X.og, p, w), ps)
                    push!(bnd, a); reach = true
                end
                for p in ps
                    (p in seen || PG.has_edge(X.og, p, w)) && continue
                    push!(seen, p); push!(todo, p)
                end
            end
            nparmax = maximum(length(parsX(a)) for a in seen)
            nparmax <= 1 && bump(:ch_single)
            reach ? bump(:ch_reach) : bump(:ch_noreach)
            Hyw = Set(holesX(y, w))
            if reach
                any(c -> supp(c, w) && supp(w, c), bnd) && bump(:ch_supp)
                any(c -> PG.has_edge(S.og, c, w), bnd) && bump(:ch_S)
                any(c -> !isempty(holesX(c, w)), bnd) && bump(:ch_hole)
                any(c -> any(l -> l in Hyw, holesX(c, w)), bnd) && bump(:ch_inh_any)
                all(c -> issubset(Set(holesX(c, w)), Hyw), bnd) && bump(:ch_inh_all)
                any(c -> c == y, bnd) && bump(:ch_y_is_bnd)
            end
            # acuerdo entre padres y tipo de hueco
            Ns(a, l) = [r for r in AX if Int(r.id.step) == l && (r == a || PG.has_edge(X.og, a, r))]
            vals(a, l) = Set(r.id for r in Ns(a, l))
            for l in holesX(y, w)
                bump(:hy_steps)
                vy = vals(y, l); vw = vals(w, l)
                isempty(intersect(vy, vw)) ? bump(:hy_value) : bump(:hy_path)
                (isempty(vy) || isempty(vw)) && bump(:hy_empty)
            end
            let lo = min(Int(y.id.step), Int(w.id.step)), hi = max(Int(y.id.step), Int(w.id.step)), H = holesX(y, w)
                any(l -> l < lo, H) && bump(:pos_below)
                any(l -> lo < l < hi, H) && bump(:pos_between)
                any(l -> l > hi, H) && bump(:pos_above)
                all(l -> l > hi, H) && bump(:pos_only_above)
            end
            ps = parsX(y)
            if length(ps) >= 2
                low = Int(y.id.step) - 1
                Il = Set(l for l in intersect([Set(holesX(p, w)) for p in ps]...) if l < low)
                isempty(Il) || bump(:two_Il)
                issubset(Il, Set(holesX(y, w))) && bump(:two_Il_sub_y)
            end
            if length(ps) >= 2
                bump(:two_par)
                Hs = [Set(holesX(p, w)) for p in ps]
                I = intersect(Hs...)
                isempty(I) ? bump(:two_noI) : bump(:two_I)
                issubset(I, Set(holesX(y, w))) && bump(:two_I_sub_y)
                # pasos de hueco de y que no son comunes a los padres
                any(l -> !(l in I), holesX(y, w)) && bump(:two_y_extra)
            end
            # hueco con las aristas de la propia X (lo que da la contradicción)
            any(0:k) do l
                (l == Int(y.id.step) || l == Int(w.id.step)) && return false
                all(r -> Int(r.id.step) != l || !(PG.has_edge(X.og, y, r) && PG.has_edge(X.og, w, r)), AX)
            end && bump(:hole_own)
            tg = get(get(TRIGS, (D, sk, k), Dict()), Set([y, w]), nothing)
            if tg === nothing
                bump(:trig_none)
            else
                bump(:trig)
                isempty(tg) && bump(:trig_emptyset)
                fullh(l) = all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), AX)
                all(fullh, tg) && bump(:trig_full_all)
                any(fullh, tg) && bump(:trig_full_any)
                HS0 = [l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(PG.has_edge(S.og, y, r) && PG.has_edge(S.og, w, r)), AX)]
                all(l -> l in HS0, tg) && bump(:trig_in_S)
                # con las aristas de las entradas del nivel SIGUIENTE (tras las llegadas)
                nxt = get(bystep, k + 1, nothing)
                if nxt !== nothing
                    adjN(a, b) = a == b || any(E -> PG.has_edge(E.og, a, b), values(nxt))
                    fullN(l) = all(r -> Int(r.id.step) != l || !(adjN(y, r) && adjN(w, r)), AX)
                    bump(:n_has)
                    all(fullN, tg) && bump(:n_trig_all)
                    any(fullN, tg) && bump(:n_trig_any)
                    all(l -> fullN(l), [l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(PG.has_edge(X.og, y, r) && PG.has_edge(X.og, w, r)), AX)]) && bump(:n_ownX_all)
                    # ¿la entrada del destino tiene y–w? (en el uso, kvA no la tiene)
                    ED = get(nxt, D, nothing)
                    (ED !== nothing && PG.has_edge(ED.og, y, w)) && bump(:n_ED_yw)
                    if !(ED !== nothing && PG.has_edge(ED.og, y, w))
                        bump(:c_n)
                        all(fullN, tg) && bump(:c_trig_allN)
                        all(fullh, tg) && bump(:c_trig_allK)
                    end
                end
                # el camino muerto: testigos de S en los pasos disparadores
                Wd = Dict(l => [r for r in alive(S) if Int(r.id.step) == l && PG.has_edge(S.og, y, r) && PG.has_edge(S.og, w, r)] for l in tg)
                all(l -> length(Wd[l]) == 1, tg) && bump(:w_single)
                all(l -> !isempty(Wd[l]), tg) && bump(:w_nonempty)
                any(r -> r in AX, (r for l in tg for r in Wd[l])) && bump(:w_someX)
                Wall = unique(r for l in tg for r in Wd[l])
                all(((a, b),) -> a == b || PG.has_edge(S.og, a, b), Iterators.product(Wall, Wall)) && bump(:w_clique)
                rq = get(REQS, (D, sk, k), nothing)
                if rq !== nothing
                    bump(:r_has)
                    reqat = Dict(Int(z.step) => z for z in rq if Int(z.step) < k)
                    isempty(reqat) && bump(:r_none_below)
                    direct = any(r -> haskey(reqat, Int(r.id.step)) && r.id != reqat[Int(r.id.step)], Wall)
                    direct && bump(:w_direct)
                    incompat(r) = any(((st, z),) -> !any(q -> q.id == z && (q == r || PG.has_edge(S.og, r, q)), alive(S)), collect(reqat))
                    any(incompat, Wall) && bump(:w_incompat_any)
                    all(incompat, Wall) && bump(:w_incompat_all)
                    # y y w son compatibles (sobreviven)
                    (incompat(y) || incompat(w)) && bump(:yw_incompat)
                    # ReqHole: un paso donde todo vecino común (en el nivel, mixto incluido) no está en S o es incompatible
                    AS2 = alive(S)
                    allK2 = Set(z for E in values(es) for z in alive(E))
                    reqhole(l) = all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)) || !(r in AS2) || incompat(r), allK2)
                    any(reqhole, 0:k-1) && bump(:reqhole)
                    # cascada de la regla de nodo desde las muertes del filtro (sin regla de parejas)
                    live = Set(r for r in AS2 if !(haskey(reqat, Int(r.id.step)) && r.id != reqat[Int(r.id.step)]))
                    changed = true
                    while changed
                        changed = false
                        for r in collect(live)
                            ok = all(0:k-1) do st
                                st == Int(r.id.step) && return true
                                any(q -> Int(q.id.step) == st && PG.has_edge(S.og, r, q), live)
                            end
                            ok || (delete!(live, r); changed = true)
                        end
                    end
                    reqhole2(l) = all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)) || !(r in live), allK2)
                    any(reqhole2, 0:k-1) && bump(:reqhole_casc)
                    (y in live && w in live) && bump(:yw_live)
                    all(r -> r in live, (r for r in AX if Int(r.id.step) < k)) && bump(:X_in_live)
                    any(reqhole, tg) && bump(:reqhole_trig)
                    # ¿y los supervivientes de X compatibles? (incompat solo de primer orden)
                    comp_surv = all(r -> !incompat(r), AX)
                    comp_surv && bump(:X_all_compat)
                    # rellenos: compatibles con los requisitos por construcción; ¿con el camino muerto?
                    for l in tg
                        fullh(l) && continue
                        for r in AX
                            (Int(r.id.step) == l && adjK(y, r) && adjK(w, r)) || continue
                            bump(:fl_r)
                            all(q -> q == r || PG.has_edge(S.og, r, q) || any(E -> PG.has_edge(E.og, r, q), values(es)), Wall) && bump(:fl_adj_path)
                        end
                    end
                end
                # los casos en que la otra entrada tapa algún paso disparador
                if !all(fullh, tg)
                    bump(:f_pairs)
                    if get(ENV, "DETAIL", "") == "1" && C[:f_pairs] <= 3
                        sid(z) = string(Int(z.id.step), ":", Int(z.id.index))
                        println(stderr, "PAIR y=", sid(y), " w=", sid(w), " k=", k, " D=", D, " trig=", sort(tg))
                        for l in sort(tg)
                            fl = fullh(l)
                            fills = [r for r in AX if Int(r.id.step) == l && adjK(y, r) && adjK(w, r)]
                            dead = [r for r in alive(S) if Int(r.id.step) == l && PG.has_edge(S.og, y, r) && PG.has_edge(S.og, w, r)]
                            nx = [r for r in AX if Int(r.id.step) == l]
                            println(stderr, "  l=", l, fl ? " LIBRE" : " TAPADO", " vivosX=", length(nx),
                                    " testigosS_muertos=", length(dead), " valores_vivosX=", sort(unique(Int(r.id.index) for r in nx)))
                            for r in fills
                                Sy = PG.has_edge(S.og, y, r); Sw = PG.has_edge(S.og, w, r)
                                src_y = [key for (key, E) in es if PG.has_edge(E.og, y, r)]
                                src_w = [key for (key, E) in es if PG.has_edge(E.og, w, r)]
                                println(stderr, "     r=", r, " S:y=", Sy, " S:w=", Sw, " y<-", src_y, " w<-", src_w)
                            end
                        end
                    end
                    Sp2 = [E for E in values(es) if E !== S]
                    for E1 in Sp2
                        PG.has_edge(E1.og, y, w) && bump(:f_E1_yw)
                        (PG.is_alive(E1.og, y) && PG.is_alive(E1.og, w)) && bump(:f_E1_alive)
                    end
                    AS = alive(S)
                    for l in tg
                        tag = fullh(l) ? "u" : "t"
                        bump(Symbol("f_", tag, "_steps"))
                        for E1 in Sp2
                            W1 = [r for r in alive(E1) if Int(r.id.step) == l && (r == y || PG.has_edge(E1.og, y, r)) &&
                                  (r == w || PG.has_edge(E1.og, w, r))]
                            isempty(W1) && bump(Symbol("f_", tag, "_noW1"))
                            for r in W1
                                bump(Symbol("f_", tag, "_w1"))
                                r in AS && bump(Symbol("f_", tag, "_w1_inS"))
                                r in AX && bump(Symbol("f_", tag, "_w1_inX"))
                                (r in AS && PG.has_edge(S.og, y, r)) && bump(Symbol("f_", tag, "_w1_Sy"))
                                (r in AS && PG.has_edge(S.og, w, r)) && bump(Symbol("f_", tag, "_w1_Sw"))
                            end
                        end
                    end
                end
                # hueco de valor en todo el nivel: vecinos (en cualquier entrada del nivel) de y y de w en l
                allK = Set(z for E in values(es) for z in alive(E))
                gv(a, l) = Set(z.id for z in allK if Int(z.id.step) == l && (z == a || adjK(a, z)))
                gval(l) = isempty(intersect(gv(y, l), gv(w, l)))
                any(gval, tg) && bump(:trig_gval_any)
                any(l -> gval(l), 0:k-1) && bump(:gval_any)
                # valor en X solamente
                xv(a, l) = Set(z.id for z in AX if Int(z.id.step) == l && (z == a || adjK(a, z)))
                any(l -> isempty(intersect(xv(y, l), xv(w, l))), tg) && bump(:trig_xval_any)
            end
            rl in (:pair, :none) ? bump(Symbol("rule_", rl)) : (bump(:rule_other); println(stderr, "RULE ", rl))
            Sp = [E for E in values(es) if E !== S]
            hS(l) = all(r -> Int(r.id.step) != l || !(PG.has_edge(S.og, y, r) && PG.has_edge(S.og, w, r)), AX)
            hF(l) = all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), AX)
            HS = [l for l in 0:k-1 if hS(l)]
            all(hF, HS) && bump(:sholes_full)
            # en los pasos del hueco de S que no son hueco completo: ¿quién tapa?
            for l in HS
                hF(l) && continue
                bump(:blk)
                for r in AX
                    Int(r.id.step) == l || continue
                    (adjK(y, r) && adjK(w, r)) || continue
                    sy = PG.has_edge(S.og, y, r); sw = PG.has_edge(S.og, w, r)
                    oy = any(E -> PG.has_edge(E.og, y, r), Sp); ow = any(E -> PG.has_edge(E.og, w, r), Sp)
                    (oy && ow) ? bump(:blk_oo) : bump(:blk_mix)
                    # ¿y, w, r vivos en la otra entrada?
                    all(E -> PG.is_alive(E.og, y) && PG.is_alive(E.og, w), Sp) && bump(:blk_yw_in_o)
                    # ¿la otra entrada tiene la arista y–w?
                    any(E -> PG.has_edge(E.og, y, w), Sp) && bump(:blk_o_has_yw)
                end
            end
            hol(adj) = any(0:k-1) do l
                all(r -> Int(r.id.step) != l || !(adj(y, r) && adj(w, r)), AX)
            end
            hol(adjK) && bump(:hole)
            hol((a, b) -> a == b || PG.has_edge(S.og, a, b)) && bump(:holeS)
            hol(adjD) && bump(:holeArr)
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:np, :hole, :holeS, :holeArr, :rule_pair, :rule_none, :rule_other, :trig, :trig_none, :trig_emptyset, :trig_full_all, :trig_full_any, :trig_in_S, :w_single, :w_nonempty, :w_someX, :w_clique, :r_has, :r_none_below, :w_direct, :w_incompat_any, :w_incompat_all, :yw_incompat, :fl_r, :fl_adj_path, :reqhole, :reqhole_trig, :reqhole_casc, :yw_live, :X_in_live, :X_all_compat, :n_has, :n_trig_all, :n_trig_any, :n_ownX_all, :n_ED_yw, :c_n, :c_trig_allN, :c_trig_allK, :f_pairs, :f_E1_yw, :f_E1_alive, :f_t_steps, :f_t_noW1, :f_t_w1, :f_t_w1_inS, :f_t_w1_inX, :f_t_w1_Sy, :f_t_w1_Sw, :f_u_steps, :f_u_noW1, :f_u_w1, :f_u_w1_inS, :f_u_w1_inX, :f_u_w1_Sy, :f_u_w1_Sw, :trig_gval_any, :gval_any, :trig_xval_any, :supp_ok, :supp_fail, :hole_own, :ch_single, :ch_reach, :ch_noreach, :ch_supp, :ch_S, :ch_hole, :ch_inh_any, :ch_inh_all, :ch_y_is_bnd, :hy_steps, :hy_value, :hy_path, :hy_empty, :two_par, :two_I, :two_noI, :two_I_sub_y, :two_y_extra, :pos_below, :pos_between, :pos_above, :pos_only_above, :two_Il, :two_Il_sub_y, :sholes_full, :blk, :blk_oo, :blk_mix, :blk_yw_in_o, :blk_o_has_yw, :abs, :abs_inX, :abs_hole, :abs_ctop, :abs_ctop_hole, :ab1, :ab1_hole, :ab1_ctop, :ab1_ctop_hole, :ab1_star, :ab1_star_hole); _unused = (:freeN, :anyfree, :mono_fail, :allP, :tN, :nfree, :tQ, :tQtop, :qfree, :qfree1, :one_sender, :nox, :rem_any, :rem_all, :holeX_free, :holeS_free, :holeX_sub, :holeS_sub, :blk_steps, :blk_r, :blk_inX, :blk_Syr, :blk_Swr, :blk_split, :blk_inEq, :max_free, :min_free, :max_free_all, :hole_common, :hole_common_free, :gap_0, :gap_1, :gap_2, :gap_3, :rq_n, :rq_max, :rq_all, :y_has, :w_has, :wk, :wk_SS, :wk_OO, :wk_mix, :wk_dead, :wk_outcone, :wk_lost_both, :wk_lost_one, :wk_BUG, :wk_inX, :wk_notX, :cone_inX, :anc_oneX, :holeL, :holeL_max, :suff, :multi, :multi2, :multi_nox, :multi_common, :multi_other, :multi_other_yw, :multi_other_hole)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDER); empty!(ARR); empty!(REMOVALS); empty!(TRIGS); empty!(REQS); empty!(REQS)
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            Probes.with(:pair_bad => on_pair_bad) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
            bystep = Dict{Int, Dict{Any, Any}}()
            for ((k, st), g) in SENDER
                g.is_valid || continue
                bystep[st] = get(bystep, st, Dict{Any, Any}())
                bystep[st][k] = g
            end
            judge_arr(bystep)
            for (st, es) in bystep
                nothing
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
