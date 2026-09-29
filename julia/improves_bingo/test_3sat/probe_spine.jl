# La espina: testigos forzados por a y t (29-sept-2026, rama reader-stuck; sonda rápida): SideKeep.
#
# Para V (estructuras al azar de la unión y núcleos fijados en un color) y cada cima t de V, L = el lado (llegada) de
# t. Restringir V a los vivos de L y a las aristas de L, y revisar (h):
#   sk_t / sk_f   — ¿sobreviven en h todos los nodos de la estrella de t en V? (fallo: alguno muere)
#   ske_f         — ¿alguna arista z–t de la estrella muere en h?
#   skt_f         — ¿muere t?
#   Si SideKeep vale, B1 sale de StarInv del lado (demostrado para llegadas).
# (Cabecera original: vía B del v208.)
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_topstar_union.jl <salida.tsv> [muestras] [semilla]
#
# Para V: (a) estructuras cerradas al azar de la unión (restringir y revisar) y (b) la unión fijada en cada color c
# (el núcleo del lector). Para cada cima t de V (paso T - 1), su estrella S(t) = vivos de V que posee t (con t):
#   pr_t / pr_f   — regla de parejas en S(t): toda pareja de V dentro de S(t) tiene en cada paso un testigo común en S(t)
#   fx_t / fx_f   — restringir V a S(t) y revisar deja S(t) entera (fx_f: pierde algo)
#   tk_f          — ... y ni siquiera sobrevive t
#   yk_f          — nodos de S(t) en el paso del remitente que mueren (lo que la vía B necesita: el testigo y su nodo)
# Prefijos r_ (estructuras al azar) y k_ (núcleos fijados en un color).

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 6
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(SEED))
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)

const SENDER = Dict{Any, Any}()
Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        key = (gpath.map_parent_id, Int(gpath.current_step))
        haskey($(SENDER), key) || ($(SENDER)[key] = deepcopy(gpath))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)


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
        LOGHOOK[] === nothing || LOGHOOK[](g, x, w, rule)
        return true
    end
end)

function restrict(g, U)
    h = deepcopy(g)
    for x in collect(alive(h))
        x in U && continue
        GraphPath.remove_node_owner!(h, x; rule = :probe)
    end
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end
pin(g, P) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(P)); g2)

function restrict_side(V, L)
    h = deepcopy(V)
    AL = alive(L)
    for x in collect(alive(h))
        x in AL && continue
        GraphPath.remove_node_owner!(h, x; rule = :probe)
    end
    for (a, b) in collect(keys(h.og.edges))
        a == b && continue
        PG.has_edge(L.og, a, b) || PG.remove_edge!(h.og, a, b; rule = :probe)
    end
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

const EXH = Ref(false)
function spine!(V, pre)
    V.is_valid || return
    og = V.og; cs = Int(V.current_step); top = cs - 1
    AV = alive(V)
    bystep = Dict{Int, Vector{PathNodeId}}()
    for z in AV
        push!(get!(bystep, Int(z.id.step), PathNodeId[]), z)
    end
    adj(a, b) = a == b || PG.has_edge(og, a, b)
    function propagate(C)
        while true
            changed = false
            for l in 0:top
                haskey(C, l) && continue
                cand = [r for r in get(bystep, l, PathNodeId[]) if all(x -> adj(x, r), values(C))]
                isempty(cand) && return :zero
                if length(cand) == 1
                    C[l] = cand[1]; changed = true
                end
            end
            changed || break
        end
        return length(C) == cs ? :full : :stuck
    end
    function dfs(C, budget)
        st = propagate(C)
        st == :zero && return false
        st == :full && return true
        budget[] <= 0 && (EXH[] = true; return false)
        budget[] -= 1
        l = first(l for l in 0:top if !haskey(C, l))
        for r in [r for r in get(bystep, l, PathNodeId[]) if all(x -> adj(x, r), values(C))]
            C2 = copy(C); C2[l] = r
            dfs(C2, budget) && return true
        end
        return false
    end
    # herencia por padres: para x y su padre p (poseídos), ¿todo vecino w de x por encima (resp. por debajo de p) posee a p?
    for x in AV
        nd = PathCollectionLines.get_node(V.table_lines, x)
        nd === nothing && continue
        ps = [p for p in nd.parents if p in AV && adj(x, p)]
        isempty(ps) && continue
        length(ps) >= 2 && bump(Symbol(pre, "h_twopar"))
        length(ps) >= 3 && bump(Symbol(pre, "h_threepar"))
        # ParentTrio: w, w' vecinos de x y entre sí, en pasos distintos al de los padres
        if length(ps) >= 2
            ws = [w for w in AV if w != x && adj(x, w) && !(w in ps) && Int(w.id.step) != Int(x.id.step) - 1]
            for i in 1:length(ws), j in i+1:length(ws)
                (w1, w2) = (ws[i], ws[j])
                (Int(w1.id.step) == Int(w2.id.step) || !adj(w1, w2)) && continue
                bump(Symbol(pre, "pt_n"))
                any(p -> adj(p, w1) && adj(p, w2), ps) || bump(Symbol(pre, "pt_fail"))
            end
        end
        for w in AV
            (w == x || !adj(x, w)) && continue
            for p in ps
                w == p && continue
                if Int(w.id.step) > Int(x.id.step)
                    bump(Symbol(pre, "h_up_n")); adj(w, p) || bump(Symbol(pre, "h_up_fail"))
                    (length(ps) >= 2 && !adj(w, p)) && bump(Symbol(pre, "h_up_fail_two"))
                elseif Int(w.id.step) < Int(p.id.step)
                    bump(Symbol(pre, "h_dn_n")); adj(w, p) || bump(Symbol(pre, "h_dn_fail"))
                    # al menos un padre de x posee a w
                    any(q -> adj(w, q), ps) || bump(Symbol(pre, "h_dn_none"))
                end
            end
        end
    end
    for t in get(bystep, top, PathNodeId[])
        for a in AV
            (a == t || !PG.has_edge(og, a, t)) && continue
            C = Dict(Int(a.id.step) => a, top => t)
            st = propagate(C)
            bump(Symbol(pre, "pairs"))
            bump(Symbol(pre, "st_", st))
            bump(Symbol(pre, "forced_steps"), length(C) - 2)
            bump(Symbol(pre, "all_steps"), cs - 2)
            if st == :full
                docpath = all(0:top-1) do l
                    nd = PathCollectionLines.get_node(V.table_lines, C[l + 1])
                    nd !== nothing && C[l] in nd.parents
                end
                docpath ? bump(Symbol(pre, "f_docpath")) : bump(Symbol(pre, "f_nodocpath"))
            end
            if st == :stuck
                # voraz: en cada paso atascado, probar CADA candidato una vez y propagar; ¿alguno lleva a contradicción?
                l0 = first(l for l in 0:top if !haskey(C, l))
                cands = [r for r in get(bystep, l0, PathNodeId[]) if all(x -> adj(x, r), values(C))]
                bad = 0
                for r in cands
                    C2 = copy(C); C2[l0] = r
                    propagate(C2) == :zero && (bad += 1)
                end
                bump(Symbol(pre, "g_cands"), length(cands))
                bump(Symbol(pre, "g_bad"), bad)
                bad > 0 && bump(Symbol(pre, "g_pair_bad"))
                # voraz completo: siempre el primer candidato
                C3 = copy(C); gst = :stuck
                while gst == :stuck
                    l1 = first(l for l in 0:top if !haskey(C3, l))
                    cs1 = [r for r in get(bystep, l1, PathNodeId[]) if all(x -> adj(x, r), values(C3))]
                    isempty(cs1) && (gst = :zero; break)
                    C3[l1] = cs1[1]
                    gst = propagate(C3)
                end
                gst == :full ? bump(Symbol(pre, "g_first_ok")) : bump(Symbol(pre, "g_first_dead"))
                # relación de los candidatos del paso atascado con lo ya elegido (documentos de V)
                for r in cands
                    rel = false
                    for (lx, x) in C
                        nd = PathCollectionLines.get_node(V.table_lines, x)
                        nd === nothing && continue
                        (lx == l0 + 1 && r in nd.parents) && (rel = true)
                        (lx == l0 - 1 && r in nd.sons) && (rel = true)
                    end
                    bump(Symbol(pre, rel ? "c_rel" : "c_norel"))
                    # ¿hay elegidos en l0±1?
                    (haskey(C, l0 + 1) || haskey(C, l0 - 1)) || bump(Symbol(pre, "c_isolated"))
                end
                if gst == :full
                    docpath = all(0:top-1) do l
                        nd = PathCollectionLines.get_node(V.table_lines, C3[l + 1])
                        nd !== nothing && C3[l] in nd.parents
                    end
                    docpath ? bump(Symbol(pre, "g_docpath")) : bump(Symbol(pre, "g_nodocpath"))
                end
                EXH[] = false
                ok = dfs(C, Ref(20000))
                ok ? bump(Symbol(pre, "stuck_clique")) : (EXH[] ? bump(Symbol(pre, "stuck_budget")) : bump(Symbol(pre, "stuck_noclique")))
            end
        end
    end
end

function judge_firstcut!(V, e, g, pre)
    V.is_valid || return
    og = V.og; top = Int(V.current_step) - 1
    AV = alive(V)
    for t in collect(get(og.alive, top, SetPathNodesId()))
        (t.parent_id === nothing || t.gparent_id === nothing) && continue
        c = t.parent_id; c2 = t.gparent_id
        S = Set(z for z in AV if z != t && PG.has_edge(og, z, t)); push!(S, t)
        # pares de la estrella en V
        spairs = Set(Set([a, b]) for (a, b) in keys(og.edges) if a != b && a in S && b in S)
        bump(Symbol(pre, "t"))
        # revisión fijada con registro
        W = deepcopy(V)
        evs = Any[]
        PathOwnersGraph.LOGHOOK[] = (gg, x, w, r) -> (gg === W.og && push!(evs, (x, w, r)))
        GraphPath.filter!(W, SetNodesId([c, c2]))
        PathOwnersGraph.LOGHOOK[] = nothing
        W.is_valid || (bump(Symbol(pre, "inval")); continue)
        # margen de las aristas hacia t
        let ogW = W.og, AW = alive(W)
            for a in S
                a == t && continue
                for l in 0:Int(V.current_step)-1
                    (l == Int(a.id.step) || l == top) && continue
                    before = [r for r in S if Int(r.id.step) == l && (r == a || PG.has_edge(og, a, r))]
                    after = [r for r in before if r in AW && a in AW && (r == a || PG.has_edge(ogW, a, r)) && PG.has_edge(ogW, r, t)]
                    bump(Symbol(pre, "m_cells"))
                    isempty(after) && bump(Symbol(pre, "m_zero"))
                    length(after) == 1 && bump(Symbol(pre, "m_one"))
                    (length(after) == 1 && length(before) > 1) && bump(Symbol(pre, "m_one_lost"))
                    length(after) < length(before) && bump(Symbol(pre, "m_shrunk"))
                end
            end
        end
        ist = [i for (i, (x, w, r)) in enumerate(evs) if Set([x, w]) in spairs]
        isempty(ist) && (bump(Symbol(pre, "nocut")); continue)
        bump(Symbol(pre, "cut"))
        bump(Symbol(pre, "cuts_n"), length(ist))
        (x0, w0, r0) = evs[ist[1]]
        bump(Symbol(pre, "first_", r0))
        ((x0 == t || w0 == t)) && bump(Symbol(pre, "first_to_t"))
        # los testigos en V de la primera pareja cortada: en el paso donde falta, ¿qué los mató antes?
        # (reconstruir el estado justo antes del corte: V menos los eventos anteriores)
        prior = Set(Set([x, w]) for (x, w, r) in evs[1:ist[1]-1])
        aliveW(z) = true
        for l in 0:Int(V.current_step)-1
            wit = [r for r in get(og.alive, l, SetPathNodesId()) if (r == x0 || PG.has_edge(og, x0, r)) && (r == w0 || PG.has_edge(og, w0, r))]
            live = [r for r in wit if !(Set([x0, r]) in prior) && !(Set([w0, r]) in prior)]
            isempty(live) || continue
            bump(Symbol(pre, "fc_steps"))
            l == top - 1 && bump(Symbol(pre, "fc_at_c"))
            l == top - 2 && bump(Symbol(pre, "fc_at_c2"))
            for r in wit
                bump(Symbol(pre, "fc_w"))
                wrong = (l == top - 1 && r.id != c) || (l == top - 2 && r.id != c2)
                wrong ? bump(Symbol(pre, "fc_w_pinned")) : bump(Symbol(pre, "fc_w_cascade"))
                r in S && bump(Symbol(pre, "fc_w_instar"))
            end
        end
    end
end

function judge_pinstar!(V, e, g, pre)
    V.is_valid || return
    og = V.og; top = Int(V.current_step) - 1
    for t in collect(get(og.alive, top, SetPathNodesId()))
        L = PG.is_alive(e.og, t) ? e : (PG.is_alive(g.og, t) ? g : nothing)
        L === nothing && continue
        t.parent_id === nothing && continue
        c = t.parent_id
        S = Set(z for z in alive(V) if z != t && PG.has_edge(og, z, t))
        W = pin(V, [c])
        bump(Symbol(pre, "t"))
        mixed = length(unique(z.id for z in alive(V) if Int(z.id.step) == top - 1)) >= 2
        mixed && bump(Symbol(pre, "mixed"))
        W.is_valid || (bump(Symbol(pre, "pin_inval")); continue)
        AW = alive(W)
        okn = issubset(S, AW) && t in AW
        oke = okn && all(z -> PG.has_edge(W.og, z, t), S)
        okn || bump(Symbol(pre, "lost_node"))
        oke || bump(Symbol(pre, "lost_edge"))
        (mixed && !oke) && bump(Symbol(pre, "mixed_fail"))
        off = count(((a, b),) -> a != b && !PG.has_edge(L.og, a, b), keys(W.og.edges))
        off == 0 ? bump(Symbol(pre, "oneside")) : bump(Symbol(pre, "offside"))
        tops = [x for x in AW if Int(x.id.step) == top]
        length(tops) >= 2 && bump(Symbol(pre, "multitop"))
        # doble fijación: padres (c) y abuelo (c')
        t.gparent_id === nothing && continue
        W2 = pin(V, [c, t.gparent_id])
        bump(Symbol(pre, "t2"))
        W2.is_valid || (bump(Symbol(pre, "pin2_inval")); continue)
        A2 = alive(W2)
        ok2 = issubset(S, A2) && t in A2 && all(z -> PG.has_edge(W2.og, z, t), S)
        ok2 || bump(Symbol(pre, "pin2_fail"))
        off2 = count(((a, b),) -> a != b && !PG.has_edge(L.og, a, b), keys(W2.og.edges))
        off2 == 0 || bump(Symbol(pre, "pin2_offside"))
    end
end

function judge_kernel!(V, e, g, pre)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    AV = alive(V)
    for t in collect(get(og.alive, top, SetPathNodesId()))
        L = PG.is_alive(e.og, t) ? e : (PG.is_alive(g.og, t) ? g : nothing)
        L === nothing && continue
        tn = PathCollectionLines.get_node(L.table_lines, t)
        pars = tn === nothing ? PathNodeId[] : [p for p in tn.parents if PG.is_alive(L.og, p)]
        star = Set(z for z in AV if z != t && PG.has_edge(og, z, t))
        pown = Set(z for z in AV if Int(z.id.step) < top && any(p -> z == p || PG.has_edge(L.og, z, p), pars))
        bump(Symbol(pre, "t"))
        star == pown ? bump(Symbol(pre, "eq")) : (issubset(star, pown) ? bump(Symbol(pre, "sub")) : bump(Symbol(pre, "other")))
        A = t.parent_id === nothing ? nothing : get(SENDER, (t.parent_id, Int(L.current_step) - 1), nothing)
        A === nothing && (bump(Symbol(pre, "noA")); continue)
        nE = 0; nA = 0
        for (a, b) in keys(og.edges)
            (a == b || !(a in star) || !(b in star)) && continue
            nE += 1
            PG.has_edge(A.og, a, b) || (nA += 1)
        end
        bump(Symbol(pre, "edges"), nE)
        bump(Symbol(pre, "edges_notA"), nA)
        nA == 0 && bump(Symbol(pre, "allA"))
        # ¿la estrella de t cabe en lo que poseen los padres en el remitente?
        all(z -> any(p -> z == p || PG.has_edge(A.og, z, p), pars), star) && bump(Symbol(pre, "star_in_Apar"))
    end
end

function judge_cut!(V, e, g, pre)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    for t in collect(get(og.alive, top, SetPathNodesId()))
        L = PG.is_alive(e.og, t) ? e : (PG.is_alive(g.og, t) ? g : nothing)
        L === nothing && continue
        S = Set(z for z in alive(V) if PG.has_edge(og, z, t)); push!(S, t)
        h = restrict(V, S)
        bump(Symbol(pre, "st"))
        h.is_valid || (bump(Symbol(pre, "inval")); continue)
        A = alive(h)
        issubset(S, A) || bump(Symbol(pre, "nodelost"))
        for (a, b) in keys(og.edges)
            (a == b || !(a in S) || !(b in S)) && continue
            side = PG.has_edge(L.og, a, b)
            bump(Symbol(pre, side ? "e_side" : "e_off"))
            if !PG.has_edge(h.og, a, b)
                bump(Symbol(pre, side ? "cut_side" : "cut_off"))
                side || continue
                # el paso libre en la estrella y los testigos de V allí
                tn = PathCollectionLines.get_node(L.table_lines, t)
                pars = tn === nothing ? PathNodeId[] : [p for p in tn.parents if PG.is_alive(L.og, p)]
                for l in 0:V.current_step-1
                    Wl = [r for r in get(og.alive, l, SetPathNodesId()) if (r == a || PG.has_edge(og, a, r)) && (r == b || PG.has_edge(og, b, r))]
                    any(r -> r in S, Wl) && continue
                    bump(Symbol(pre, "fs"))
                    isempty(Wl) && bump(Symbol(pre, "fs_now"))
                    for r in Wl
                        bump(Symbol(pre, "fw"))
                        anyp = any(p -> PG.has_edge(L.og, r, p), pars)
                        anyp ? bump(Symbol(pre, "fw_parent_has")) : bump(Symbol(pre, "fw_hist_incompat"))
                        PG.is_alive(L.og, r) || bump(Symbol(pre, "fw_notL"))
                    end
                    break
                end
            end
        end
    end
end

function judge_side!(V, e, g, pre)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    for t in collect(get(og.alive, top, SetPathNodesId()))
        L = PG.is_alive(e.og, t) ? e : (PG.is_alive(g.og, t) ? g : nothing)
        L === nothing && (bump(Symbol(pre, "noside")); continue)
        S = Set(z for z in alive(V) if PG.has_edge(og, z, t)); push!(S, t)
        h = restrict_side(V, L)
        A = h.is_valid ? alive(h) : Set{PathNodeId}()
        bump(Symbol(pre, "sk_t"))
        issubset(S, A) || bump(Symbol(pre, "sk_f"))
        t in A || bump(Symbol(pre, "skt_f"))
        any(z -> z != t && !(h.is_valid && PG.has_edge(h.og, z, t)), S) && bump(Symbol(pre, "ske_f"))
    end
end

function judge!(V, k, pre)
    V.is_valid || return
    og = V.og; top = V.current_step - 1
    for t in collect(get(og.alive, top, SetPathNodesId()))
        S = Set(z for z in alive(V) if PG.has_edge(og, z, t))
        push!(S, t)
        # (i) regla de parejas dentro de la estrella
        ok = true
        for (y, w) in keys(og.edges)
            (y in S && w in S) || continue
            for l in 0:V.current_step-1
                any(r -> r in S && PG.has_edge(og, y, r) && PG.has_edge(og, w, r), get(og.alive, l, SetPathNodesId())) && continue
                ok = false; break
            end
            ok || break
        end
        bump(Symbol(pre, "pr_t")); ok || bump(Symbol(pre, "pr_f"))
        # (ii) restringir y revisar
        h = restrict(V, S)
        A = h.is_valid ? alive(h) : Set{PathNodeId}()
        bump(Symbol(pre, "fx_t"))
        A == S || bump(Symbol(pre, "fx_f"))
        t in A || bump(Symbol(pre, "tk_f"))
        for y in S
            y.id.step == k || continue
            bump(Symbol(pre, "yk_t"))
            y in A || bump(Symbol(pre, "yk_f"))
        end
    end
end

const SIDES = Ref{Any}(nothing)
function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    k = u.current_step - 2
    k >= 0 || return
    cols = unique(x.id for x in get(u.og.alive, k, SetPathNodesId()))
    spine!(u, "u_")
    for _ in 1:SAMPLES
        p = rand(RNG[], (0.5, 0.7, 0.9))
        spine!(restrict(u, Set(x for x in alive(u) if rand(RNG[]) < p)), "r_")
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = Symbol[]
    for pre in ("u_", "r_"), c in ("pairs", "st_full", "st_stuck", "st_zero", "forced_steps", "all_steps", "stuck_clique", "stuck_noclique", "stuck_budget", "g_cands", "g_bad", "g_pair_bad", "g_first_ok", "g_first_dead", "c_rel", "c_norel", "c_isolated", "g_docpath", "g_nodocpath", "f_docpath", "f_nodocpath", "h_twopar", "h_threepar", "pt_n", "pt_fail", "h_up_n", "h_up_fail", "h_up_fail_two", "h_dn_n", "h_dn_fail", "h_dn_none")
        push!(cols, Symbol(pre, c))
    end
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDER)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b))),
                                 :join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
