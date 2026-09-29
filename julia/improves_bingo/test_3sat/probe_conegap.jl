# ConeGap por dentro (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_cone.jl <salida.tsv>
#
# A, B entradas distintas del nivel N (current_step N); Q grupo (id, padre) de cimas de A = padres de un t. Pareja
# y–w de B, no de A, en star_A(Q) (CrossAt). Antepasados por ids: p padre de q ⇔ p.id = q.parent_id y
# p.parent_id = q.gparent_id; la entrada de p en el nivel s es la de clave p.id. T_s antepasados del nivel s;
# C_s = vecinos (en su entrada) de T_s, con T_s; E_s = aristas de todas las entradas del nivel s.
#   Free_s: hay un paso l < s sin testigo común en C_s con E_s.
#   Clases en el nivel s: N (ningún antepasado común a y, w), Q (alguno común y con la arista y–w en su entrada),
#   P (comunes, ninguno con la arista). trans = el nivel más alto con clase ≠ P.
#   mono_fail: Free_s y no Free_{s+1} (debe ser 0). nfree: en trans N, Free_trans (debe ser 100 %).
#   qfree / qfree1: en trans Q, Free_trans / Free_{trans+1}.

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

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        key = (gpath.map_parent_id, Int(gpath.current_step))
        haskey($(SENDER), key) || ($(SENDER)[key] = deepcopy(gpath))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
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


function judge(A, B, bystep, N)
    oa = A.og; ob = B.og
    for ((_, _), Q) in groups_of(A)
        SQ = star(A, Q)
        for (y, w) in keys(ob.edges)
            (y == w || !(y in SQ) || !(w in SQ) || PG.has_edge(oa, y, w)) && continue
            bump(:np)
            mstep = max(Int(y.id.step), Int(w.id.step))
            T = collect(Q)
            free = Dict{Int, Bool}()
            freeset = Dict{Int, Vector{Int}}()
            anc = Dict{Int, Vector{PathNodeId}}()
            cas = Dict{Int, Vector{PathNodeId}}()
            cls = Dict{Int, Symbol}()
            s = N
            while s > mstep && !isempty(T)
                es = get(bystep, s, nothing)
                es === nothing && break
                ogs = [p.og for p in values(es)]
                adjL(a, b) = a == b || any(o -> PG.has_edge(o, a, b), ogs)
                ent(p) = get(es, p.id, nothing)
                Cn = Set{PathNodeId}(T)
                for p in T
                    E = ent(p); E === nothing && continue
                    for z in alive(E)
                        PG.has_edge(E.og, z, p) && push!(Cn, z)
                    end
                end
                freeset[s] = [l for l in 0:s-1 if all(r -> Int(r.id.step) != l || !(adjL(y, r) && adjL(w, r)), Cn)]
                free[s] = !isempty(freeset[s])
                anc[s] = copy(T)
                eadj(E, a, b) = a == b || PG.has_edge(E.og, a, b)
                CA = [p for p in T if (E = ent(p); E !== nothing && eadj(E, y, p) && eadj(E, w, p))]
                cas[s] = CA
                cls[s] = isempty(CA) ? :N : (any(p -> PG.has_edge(ent(p).og, y, w), CA) ? :Q : :P)
                # padres
                prev = get(bystep, s - 1, nothing)
                prev === nothing && break
                T2 = PathNodeId[]
                for q in T
                    q.parent_id === nothing && continue
                    E = get(prev, q.parent_id, nothing); E === nothing && continue
                    for p in tops(E)
                        (p.id == q.parent_id && p.parent_id == q.gparent_id) && push!(T2, p)
                    end
                end
                T = unique(T2)
                s -= 1
            end
            haskey(free, N) && free[N] && bump(:freeN)
            any(values(free)) && bump(:anyfree)
            for (k, v) in free
                v && haskey(free, k + 1) && !free[k + 1] && (bump(:mono_fail); break)
            end
            ks = sort([k for (k, c) in cls if c != :P], rev = true)
            if isempty(ks)
                bump(:allP); continue
            end
            k = ks[1]
            if cls[k] == :N
                bump(:tN); free[k] && bump(:nfree)
            else
                bump(:tQ); free[k] && bump(:qfree); get(free, k + 1, false) && bump(:qfree1)
                k == N && bump(:tQtop)
                k == N && continue
                s1 = k + 1
                FC = freeset[s1]
                length(unique(q.parent_id for q in anc[s1])) == 1 && bump(:one_sender)
                rems = Any[]
                for q in cas[s1]
                    S = get(get(bystep, k, Dict()), q.parent_id, nothing)
                    X = get(ARR, (q.id, q.parent_id, k), nothing)
                    (S === nothing || X === nothing) && (bump(:nox); continue)
                    PG.has_edge(S.og, y, w) && push!(rems, (q, S, X))
                end
                isempty(rems) || bump(:rem_any)
                length(rems) == length(cas[s1]) && bump(:rem_all)
                hx = false; hxs = false; hsub = false; hsubS = false
                for (q, S, X) in rems
                    AX = alive(X)
                    holeX = [l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(PG.has_edge(X.og, y, r) && PG.has_edge(X.og, w, r)), AX)]
                    holeS = [l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(PG.has_edge(S.og, y, r) && PG.has_edge(S.og, w, r)), AX)]
                    any(l -> l in FC, holeX) && (hx = true)
                    any(l -> l in FC, holeS) && (hxs = true)
                    (!isempty(holeX) && all(l -> l in FC, holeX)) && (hsub = true)
                    (!isempty(holeS) && all(l -> l in FC, holeS)) && (hsubS = true)
                    # quién tapa los pasos del hueco G1 que no son libres en el cono
                    esK = get(bystep, s1, Dict())
                    for l in holeS
                        l in FC && continue
                        bump(:blk_steps)
                        Cn = Set{PathNodeId}(anc[s1])
                        for p in anc[s1]
                            E = get(esK, p.id, nothing); E === nothing && continue
                            for z in alive(E); PG.has_edge(E.og, z, p) && push!(Cn, z); end
                        end
                        for r in Cn
                            Int(r.id.step) == l || continue
                            ey = [k2 for (k2, E) in esK if (r == y || PG.has_edge(E.og, y, r))]
                            ew = [k2 for (k2, E) in esK if (r == w || PG.has_edge(E.og, w, r))]
                            (isempty(ey) || isempty(ew)) && continue
                            bump(:blk_r)
                            r in AX && bump(:blk_inX)
                            PG.has_edge(S.og, y, r) && bump(:blk_Syr)
                            PG.has_edge(S.og, w, r) && bump(:blk_Swr)
                            isempty(intersect(ey, ew)) && bump(:blk_split)
                            (q.id in ey && q.id in ew) && bump(:blk_inEq)
                        end
                    end
                end
                if !isempty(rems)
                    hs_all = [[l for l in 0:k-1 if all(r -> Int(r.id.step) != l ||
                               !(PG.has_edge(S.og, y, r) && PG.has_edge(S.og, w, r)), alive(X))] for (q, S, X) in rems]
                    any(H -> !isempty(H) && maximum(H) in FC, hs_all) && bump(:max_free)
                    any(H -> !isempty(H) && minimum(H) in FC, hs_all) && bump(:min_free)
                    all(H -> !isempty(H) && maximum(H) in FC, hs_all) && bump(:max_free_all)
                    # hueco común a todas las llegadas que quitan
                    for ((q, S, X), H) in zip(rems, hs_all)
                        isempty(H) && continue
                        rq = get(REQS, (q.id, q.parent_id, k), nothing)
                        rq === nothing && continue
                        rsteps = Set(Int(z.step) for z in rq)
                        bump(:rq_n)
                        maximum(H) in rsteps && bump(:rq_max)
                        all(l -> l in rsteps, H) && bump(:rq_all)
                        # en el paso del hueco, ¿y o w poseen algún nodo requerido vivo en X?
                        l = maximum(H)
                        req_alive = [r for r in alive(X) if Int(r.id.step) == l]
                        any(r -> PG.has_edge(S.og, y, r), req_alive) && bump(:y_has)
                        any(r -> PG.has_edge(S.og, w, r), req_alive) && bump(:w_has)
                    end
                    # seguir a los testigos del nivel k en el paso más alto del hueco
                    function coneof(sl)
                        es = get(bystep, sl, Dict())
                        Cn = Set{PathNodeId}(anc[sl])
                        for p in anc[sl]
                            E = get(es, p.id, nothing); E === nothing && continue
                            for z in alive(E); PG.has_edge(E.og, z, p) && push!(Cn, z); end
                        end
                        return Cn, es
                    end
                    haskey(anc, k) && haskey(anc, s1) || @goto skip
                    Ck, esk = coneof(k)
                    Ck1, esk1 = coneof(s1)
                    for ((q, S, X), H) in zip(rems, hs_all)
                        isempty(H) && continue
                        l = maximum(H)
                        for r in Ck
                            Int(r.id.step) == l || continue
                            ay = [key for (key, E) in esk if r == y || PG.has_edge(E.og, y, r)]
                            aw = [key for (key, E) in esk if r == w || PG.has_edge(E.og, w, r)]
                            (isempty(ay) || isempty(aw)) && continue
                            bump(:wk)
                            sk = q.parent_id   # clave de S
                            (sk in ay && sk in aw) && bump(:wk_SS)
                            (!(sk in ay) && !(sk in aw)) && bump(:wk_OO)
                            ((sk in ay) != (sk in aw)) && bump(:wk_mix)
                            aliveK1 = any(E -> PG.is_alive(E.og, r), values(esk1))
                            by1 = any(E -> r == y || PG.has_edge(E.og, y, r), values(esk1))
                            bw1 = any(E -> r == w || PG.has_edge(E.og, w, r), values(esk1))
                            if !aliveK1
                                bump(:wk_dead)
                            elseif !(r in Ck1)
                                bump(:wk_outcone)
                            elseif !by1 && !bw1
                                bump(:wk_lost_both)
                            elseif !by1 || !bw1
                                bump(:wk_lost_one)
                            else
                                bump(:wk_BUG)
                            end
                            # ¿mueren r, o la arista, dentro de X?
                            PG.is_alive(X.og, r) ? bump(:wk_inX) : bump(:wk_notX)
                        end
                    end
                    # ¿cabe el cono del nivel k+1 en X? ¿hay hueco local con las aristas de todo el nivel k?
                    adjK(a, b) = a == b || any(E -> PG.has_edge(E.og, a, b), values(esk))
                    inx = false; hl = false; hlmax = false; ids1 = false
                    for ((q, S, X), H) in zip(rems, hs_all)
                        AX = alive(X)
                        all(r -> r in AX, Ck1) && (inx = true)
                        all(p -> p.id == q.id && p.parent_id == q.parent_id, anc[s1]) && (ids1 = true)
                        HL = [l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), AX)]
                        isempty(HL) || (hl = true)
                        (!isempty(H) && maximum(H) in HL) && (hlmax = true)
                    end
                    inx && bump(:cone_inX); ids1 && bump(:anc_oneX); hl && bump(:holeL); hlmax && bump(:holeL_max)
                    (inx && hl) && bump(:suff)
                    if !inx
                        bump(:multi)
                        # llegadas que llevan antepasados del nivel k+1: (destino, remitente)
                        arrs = unique([(p.id, p.parent_id) for p in anc[s1]])
                        length(arrs) == 2 && bump(:multi2)
                        Xs = [get(ARR, (a[1], a[2], k), nothing) for a in arrs]
                        any(isnothing, Xs) && (bump(:multi_nox); @goto skip)
                        # hueco en la parte del cono de cada llegada (vecinos de los antepasados en ella), aristas del nivel k
                        function part(X, a)
                            ps = [p for p in anc[s1] if (p.id, p.parent_id) == a]
                            Set(z for z in alive(X) if any(p -> z == p || PG.has_edge(X.og, z, p), ps))
                        end
                        parts = [part(X, a) for (X, a) in zip(Xs, arrs)]
                        HLs = [Set(l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), P)) for P in parts]
                        isempty(intersect(HLs...)) || bump(:multi_common)
                        # llegadas sin antepasado común (no quitan): ¿y, w vivos en ellas?
                        for (X, a) in zip(Xs, arrs)
                            any(t3 -> t3[3] === X, rems) && continue
                            bump(:multi_other)
                            (PG.is_alive(X.og, y) && PG.is_alive(X.og, w)) && bump(:multi_other_yw)
                            HLo = Set(l for l in 0:k-1 if all(r -> Int(r.id.step) != l || !(adjK(y, r) && adjK(w, r)), alive(X)))
                            isempty(HLo) || bump(:multi_other_hole)
                        end
                    end
                    @label skip
                    common = intersect([Set(H) for H in hs_all]...)
                    isempty(common) || bump(:hole_common)
                    any(l -> l in FC, common) && bump(:hole_common_free)
                    for H in hs_all
                        isempty(H) && continue
                        bump(Symbol("gap_", clamp(k - 1 - maximum(H), 0, 3)))
                    end
                end
                hx && bump(:holeX_free); hxs && bump(:holeS_free); hsub && bump(:holeX_sub); hsubS && bump(:holeS_sub)
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:np, :freeN, :anyfree, :mono_fail, :allP, :tN, :nfree, :tQ, :tQtop, :qfree, :qfree1, :one_sender, :nox, :rem_any, :rem_all, :holeX_free, :holeS_free, :holeX_sub, :holeS_sub, :blk_steps, :blk_r, :blk_inX, :blk_Syr, :blk_Swr, :blk_split, :blk_inEq, :max_free, :min_free, :max_free_all, :hole_common, :hole_common_free, :gap_0, :gap_1, :gap_2, :gap_3, :rq_n, :rq_max, :rq_all, :y_has, :w_has, :wk, :wk_SS, :wk_OO, :wk_mix, :wk_dead, :wk_outcone, :wk_lost_both, :wk_lost_one, :wk_BUG, :wk_inX, :wk_notX, :cone_inX, :anc_oneX, :holeL, :holeL_max, :suff, :multi, :multi2, :multi_nox, :multi_common, :multi_other, :multi_other_yw, :multi_other_hole)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDER); empty!(ARR); empty!(REQS)
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            bystep = Dict{Int, Dict{Any, Any}}()
            for ((k, st), g) in SENDER
                g.is_valid || continue
                bystep[st] = get(bystep, st, Dict{Any, Any}())
                bystep[st][k] = g
            end
            for (st, es) in bystep
                st < 3 && continue
                for A in values(es), B in values(es)
                    A === B && continue
                    judge(A, B, bystep, st)
                end
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
