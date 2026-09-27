# Entrada filtrada (lean/improves_bin, PieceFilter.filter_in_piece): ¿regla local que la dé por inducción de arriba
# abajo en el kernel filtrado? En cada join J con piezas P_i (claves k_i), para q nodo antiguo (paso < n) y
# v ∈ J(q) con v ∉ P_i(q):
#   SL:  ningún hijo c de q en J, nodo de P_i, tiene v ∈ P_i(c)        (subida por hijos)
#   SLa: igual, solo hijos por enlaces de P_i
#   PL:  ningún padre c de q en J, nodo de P_i, tiene v ∈ P_i(c)       (bajada por padres)
#   julia --project=../.. lift_probe.jl f1.cnf ...
include("./../../src/main.jl")
function nodes(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; D[pid] = node; end
    D
end
tab(n) = (S = Set{PathNodeId}(); for (_, set) in n.owners.table; union!(S, set); end; S)
function probe(path)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    st = Dict{String, Int}(); bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(get!(pieces, d, Any[]), p)
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            DJ = nodes(g); TJ = Dict(r => tab(n) for (r, n) in DJ)
            for p in ps
                DP = nodes(p); TP = Dict(r => tab(n) for (r, n) in DP)
                for (q, nq) in DJ
                    q.id.step < s1 - 1 || continue
                    haskey(DP, q) || continue
                    for v in TJ[q]
                        v in TP[q] && continue
                        bump("entradas ajenas a la pieza")
                        lift(cs) = any(c -> haskey(DP, c) && (v in TP[c]), cs)
                        bump(lift(nq.sons) ? "SL FALLA" : "SL ok")
                        bump(lift(DP[q].sons) ? "SLa FALLA" : "SLa ok")
                        bump(lift(nq.parents) ? "PL FALLA" : "PL ok")
                        # caso difícil: v por debajo de q
                        v.id.step < q.id.step || (bump("  v por encima o igual"); continue)
                        bump("  v por debajo")
                        c1 = any(c -> haskey(DP, c) && (v in TP[c]) && (q in TP[c]), nq.sons)
                        c2 = all(t -> any(r -> r.id.step == t && (q in TP[r]) && (v in TP[r]), keys(DP)), q.id.step+1:s1)
                        # además v posee q en J y hay testigo en cada paso por debajo de q, en J
                        bump(c1 ? "  SL2 FALLA (hijo co-posee q y v en P)" : "  SL2 ok")
                        bump(c2 ? "  C2 FALLA (co-poseídos en P en todo paso sobre q)" : "  C2 ok")
                        bump(c1 && c2 ? "  C1∧C2 FALLA" : "  C1∧C2 ok")
                        fw = all(t -> t == q.id.step || t == v.id.step ||
                            any(r -> r.id.step == t && (q in TP[r]) && (v in TP[r]), keys(DP)), 0:s1)
                        bump(fw ? "  FW FALLA (testigos en P en todo paso)" : "  FW ok")
                        if fw
                            miss = [t for t in 0:s1 if t != q.id.step && t != v.id.step &&
                                !any(r -> r.id.step == t && (q in TJ[r]) && (v in TJ[r]) && haskey(DP, r), keys(DJ))]
                            bump("  FW falla: v.paso=$(v.id.step) q.paso=$(q.id.step) top=$s1")
                        end
                    end
                end
            end
        end)
    end
    st
end
tot = Dict{String, Int}()
for f in ARGS
    s = try probe(f) catch err; println("$(basename(f)): SALTADA ($err)"); continue end
    for (k, v) in s; tot[k] = get(tot, k, 0) + v; end
end
println("── total"); for (k, v) in sort(collect(tot)); println("  $k: $v"); end
