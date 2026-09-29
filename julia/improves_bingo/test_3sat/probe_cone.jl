# El cono de antepasados (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
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
                free[s] = any(0:s-1) do l
                    all(r -> Int(r.id.step) != l || !(adjL(y, r) && adjL(w, r)), Cn)
                end
                eadj(E, a, b) = a == b || PG.has_edge(E.og, a, b)
                CA = [p for p in T if (E = ent(p); E !== nothing && eadj(E, y, p) && eadj(E, w, p))]
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
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:np, :freeN, :anyfree, :mono_fail, :allP, :tN, :nfree, :tQ, :tQtop, :qfree, :qfree1)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDER)
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
