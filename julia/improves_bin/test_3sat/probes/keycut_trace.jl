# Traza de los fallos de KTriK (M1bOwn.lean, §4.2ο.2). Para J|R válido con p–v testigos por la clave k en cada paso pero
# v ∉ T_{P_k}(p), rehace el review de J|(R+k) operación por operación (filter_require!, y por vuelta: clean,
# pair, links, parents, sons, links) y anota la primera que rompe p–v (p muere, v muere, o sale v de T(p) / p de T(v)).
# Motivo, con las tablas de justo antes de esa operación:
#   parents: ¿v está en la unión de los padres de p? (y p en la de v)   sons: lo mismo con los hijos
#   pair: primer paso l en que T(p) y T(v) no comparten                   clean: ¿quién muere?
#   julia --project=../.. keycut_trace.jl f1.cnf ...
include("./keytri_common.jl")
const GP = GraphPath
alive(g, p, v) = (U = tables(g); haskey(U, p) && haskey(U, v) && v in U[p] && p in U[v])
function nbunion(g, p, field)
    n = PathCollectionLines.get_node(g.table_lines, p); n === nothing && return Set{PathNodeId}()
    S = Set{PathNodeId}()
    for c in getfield(n, field)
        nc = PathCollectionLines.get_node(g.table_lines, c); nc === nothing && continue
        for (_, set) in nc.owners.table; union!(S, set); end
    end
    S
end
# Rehace pair_consistency_after_clean! por fases: fase 1 (parejas malas), fase 2 (quitarlas), purga; qué rompe p–v.
function pair_detail(g0, p, v, top)
    g = deepcopy(g0); rnd = 0
    while g.is_valid && g.table_lines.is_valid
        rnd += 1
        U = tables(g)
        bad = Tuple{PathNodeId, PathNodeId}[]
        for (x, Tx) in U, w in Tx
            (w == x || !haskey(U, w)) && continue
            PathDocumentOwners.shares_every_step(PathCollectionLines.get_node(g.table_lines, x).owners,
                PathCollectionLines.get_node(g.table_lines, w).owners) || push!(bad, (x, w))
        end
        isempty(bad) && return "pair: nada (¿?)"
        for (x, w) in bad
            nx = PathCollectionLines.get_node(g.table_lines, x); nw = PathCollectionLines.get_node(g.table_lines, w)
            nx !== nothing && PathDocumentNode.remove_owner!(nx, w); nw !== nothing && PathDocumentNode.remove_owner!(nw, x)
        end
        pv = [b for b in bad if b[1] in (p, v) || b[2] in (p, v)]
        alive(g, p, v) || return "pair ronda $rnd fase 2: p–v es mala ($(length(bad)) malas)"
        before = Set(keys(tables(g)))
        g.review_owners = true
        redirect_stdout(devnull) do; GP.clean_invalid_nodes!(g); end
        U2 = tables(g)
        dead = setdiff(before, Set(keys(U2)))
        if !alive(g, p, v)
            who = !haskey(U2, p) ? "muere p" : !haskey(U2, v) ? "muere v" : "sale la entrada"
            ds = sort(unique([d.id.step for d in dead]))
            return "pair ronda $rnd purga: $who; mueren $(length(dead)) nodos (pasos $ds); malas con p o v: $(length(pv)) de $(length(bad))"
        end
    end
    "pair: no se rompe (¿?)"
end
function reason(op, g, p, v, top)
    U = tables(g)
    op == :clean && return "muere " * (haskey(U, p) ? "" : "p ") * (haskey(U, v) ? "" : "v ") * "(antes de la op)"
    if op == :pair
        for l in 0:top
            any(r -> r.id.step == l && r in U[v], U[p]) || return "pair: sin común en l=$l"
        end
        return pair_detail(g, p, v, top)
    end
    if op in (:parents, :sons)
        f = op == :parents ? :parents : :sons
        a = v in nbunion(g, p, f); b = p in nbunion(g, v, f)
        return "$op: v∈∪$(f)(p)=$a, p∈∪$(f)(v)=$b"
    end
    string(op)
end
function trace(G, k, p, v, top, st)
    f = deepcopy(G)
    ops = Tuple{Symbol, Function}[]
    step!(op, fn) = begin
        before = deepcopy(f)
        redirect_stdout(devnull) do; fn(f); end
        alive(f, p, v) && return nothing
        return (op, reason(op, before, p, v, top))
    end
    r = step!(:require, g -> GP.filter_require!(g, k)); r !== nothing && return (0, r...)
    round = 0
    while f.is_valid && f.review_owners
        round += 1
        f.review_owners = false
        for (op, fn) in ((:clean, GP.clean_invalid_nodes!), (:pair, GP.pair_consistency_after_clean!),
                         (:links, GP.prune_stale_links!), (:parents, GP.review_owners_parents_sons!),
                         (:sons, GP.review_owners_sons_parents!), (:links, GP.prune_stale_links!))
            op in (:parents, :sons) && (f.review_owners = true)   # make_review llama a los dos pases con la marca puesta
            r = step!(op, fn); r !== nothing && return (round, r...)
        end
    end
    (round, :ninguna, f.is_valid ? "p–v sobrevive (¡M1bLowOwn falla!)" : "J|(R+k) inválido")
end
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
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
                            UP = get(Ps, k, nothing); UP === nothing && continue
                            (haskey(UP, p) && v in UP[p]) && continue
                            round, op, why = trace(G, k, p, v, top, st)
                            bump("vuelta $round, $op: $why")
                            get(st, "ej", 0) < 12 && (bump("ej"); println("$(basename(path)) cima $top R=$R k=$k p=$(p.id)←$(p.parent_id) v=$(v.id)←$(v.parent_id): vuelta $round $op — $why"))
                        end
                    end
                end
            end
        end)
    end
end
run_all(probe)
