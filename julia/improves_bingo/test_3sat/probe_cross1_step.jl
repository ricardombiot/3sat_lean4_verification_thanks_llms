# La inducción de CrossAt1 (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_cross1_step.jl <salida.tsv>
#
# A, B entradas distintas del paso N; Q grupo (id, padre = c) de cimas de A; SQ su estrella en A. Pareja y–w de B, no
# de A, en SQ, con una cima COMÚN en Q (CrossAt1). Ac = entrada del paso N-1 de clave c. Casos:
#   removed (y–w de Ac); nocommon (ausente, ninguna cima de Ac posee a los dos); common (alguna sí).
#   nocommon: kfree (el paso de las cimas de Ac está libre en SQ con aristas de A ∪ B; debe ser 100 %).
#   common: para cada subgrupo G de Ac (cimas con el mismo padre) con una cima común, Fg = pasos libres en star(Ac, G)
#   con aristas de todas las entradas del paso N-1; ih (algún Fg no vacío); inh (algún paso de algún Fg libre en SQ
#   con A ∪ B); inh_all (todo Fg ⊆ libres de SQ); inh_top (algún Fg contiene el paso de las cimas de Ac);
#   xw (en los fallos de inh_all, testigo que tapa: bajo otro subgrupo de Ac).
#   free (CrossAt1 en SQ, con A ∪ B: algún paso libre; debe ser 100 %).

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


function judge(A, B, prev, prev2)
    oa = A.og; ob = B.og
    adjAB(a, b) = PG.has_edge(oa, a, b) || PG.has_edge(ob, a, b)
    for ((_, pid), Q) in groups_of(A)
        SQ = star(A, Q)
        Ac = pid === nothing ? nothing : get(prev, pid, nothing)
        freeSQ(y, w, l) = (l != y.id.step && l != w.id.step) &&
            all(r -> r.id.step != l || !(adjAB(y, r) && adjAB(w, r)), SQ)
        for (y, w) in keys(ob.edges)
            (y == w || !(y in SQ) || !(w in SQ) || PG.has_edge(oa, y, w)) && continue
            any(q -> PG.has_edge(oa, y, q) && PG.has_edge(oa, w, q), Q) || continue
            bump(:np)
            any(l -> freeSQ(y, w, l), 0:Int(A.current_step)-1) && bump(:free)
            if Ac === nothing
                bump(:noAc); continue
            end
            if PG.has_edge(Ac.og, y, w)
                bump(:removed); continue
            end
            ktop = Int(Ac.current_step) - 1
            ctops = [p for p in tops(Ac) if PG.has_edge(Ac.og, y, p) && PG.has_edge(Ac.og, w, p)]
            if isempty(ctops)
                bump(:nocommon)
                freeSQ(y, w, ktop) && bump(:kfree)
                continue
            end
            bump(:common)
            ogs = [p.og for p in values(prev)]
            adj(a, b) = any(o -> PG.has_edge(o, a, b), ogs)
            gs = groups_of(Ac)
            Fs = Vector{Vector{Int}}()
            for (_, G) in gs
                any(p -> p in ctops, G) || continue
                S = star(Ac, G)
                push!(Fs, [l for l in 0:Int(Ac.current_step)-1 if l != y.id.step && l != w.id.step &&
                           all(r -> r.id.step != l || !(adj(y, r) && adj(w, r)), S)])
            end
            any(!isempty, Fs) && bump(:ih)
            any(F -> any(l -> freeSQ(y, w, l), F), Fs) && bump(:inh)
            any(F -> !isempty(F) && all(l -> freeSQ(y, w, l), F), Fs) && bump(:inh_all)
            any(F -> ktop in F, Fs) && bump(:inh_top)
            # P*: subgrupos de Ac con algún hijo vivo en Q; estrella en Ac; pasos libres con aristas de todas las entradas
            gps = Set(q.gparent_id for q in Q)
            Ps = [p for p in tops(Ac) if p.parent_id in gps]
            Ss = star(Ac, Ps)
            Fst = [l for l in 0:Int(Ac.current_step)-1 if l != y.id.step && l != w.id.step &&
                   all(r -> r.id.step != l || !(adj(y, r) && adj(w, r)), Ss)]
            length(gps) >= 2 && bump(:two_sub)
            isempty(Fst) || bump(:pstar)
            all(l -> freeSQ(y, w, l), Fst) && bump(:pstar_sub)
            # nivel 2: las cimas de P* vienen de las entradas prev2[b], b ∈ padres de P*
            prev2 === nothing && continue
            Es = [get(prev2, b, nothing) for b in Set(p.parent_id for p in Ps)]
            any(isnothing, Es) && (bump(:l2_noentry); continue)
            bump(:l2)
            k2 = Int(Ac.current_step) - 2
            if any(E -> PG.has_edge(E.og, y, w), Es)
                bump(:l2_removed); continue
            end
            ct2 = [(E, p) for E in Es for p in tops(E) if PG.has_edge(E.og, y, p) && PG.has_edge(E.og, w, p)]
            freeW(l) = l != y.id.step && l != w.id.step && all(r -> r.id.step != l || !(adj(y, r) && adj(w, r)), Ss)
            if isempty(ct2)
                bump(:l2_nocommon); freeW(k2) && bump(:l2_kfree)
            else
                bump(:l2_common)
                ogs2 = [p.og for p in values(prev2)]
                adj2(a, b) = any(o -> PG.has_edge(o, a, b), ogs2)
                # P** en cada entrada: cimas cuyo hijo está en P*; testigos: unión de estrellas en las entradas
                W2 = Set{PathNodeId}()
                for E in Es
                    gp = Set(p.gparent_id for p in Ps if p.parent_id == first(tops(E)).id)
                    union!(W2, star(E, [p for p in tops(E) if p.parent_id in gp]))
                end
                F2 = [l for l in 0:k2 if l != y.id.step && l != w.id.step &&
                      all(r -> r.id.step != l || !(adj2(y, r) && adj2(w, r)), W2)]
                isempty(F2) || bump(:l2_free)
                (!isempty(F2) && all(freeW, F2)) && bump(:l2_sub)
                # sólo con la entrada de la cima común (como un solo remitente)
                E1 = first(ct2)[1]
                gp1 = Set(p.gparent_id for p in Ps if p.parent_id == first(tops(E1)).id)
                W1 = star(E1, [p for p in tops(E1) if p.parent_id in gp1])
                F1 = [l for l in 0:k2 if l != y.id.step && l != w.id.step &&
                      all(r -> r.id.step != l || !(adj2(y, r) && adj2(w, r)), W1)]
                any(freeW, F1) && bump(:l2_one)
            end
            if get(ENV, "DETAIL", "") == "1" && C[:common] <= 12
                okl = [l for l in 0:Int(A.current_step)-1 if freeSQ(y, w, l)]
                println(stderr, "N=", A.current_step, " y=", y, " w=", w, " ktop=", ktop, " Fs=", Fs, " freeSQ=", okl)
                for F in Fs, l in F
                    freeSQ(y, w, l) && continue
                    for r in SQ
                        (r.id.step == l && adjAB(y, r) && adjAB(w, r)) || continue
                        vq = [q for q in Q if PG.has_edge(oa, r, q)]
                        par = [p for p in tops(Ac) if PG.has_edge(Ac.og, r, p)]
                        println(stderr, "   l=", l, " r=", r, " inAc=", PG.is_alive(Ac.og, r),
                                " prevAdj=", adj(y, r), adj(w, r), " viaQ=", vq, " rTopsAc=", par, " ctops=", ctops)
                    end
                end
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:np, :free, :noAc, :removed, :nocommon, :kfree, :common, :ih, :inh, :inh_all, :inh_top, :two_sub, :pstar, :pstar_sub, :l2_noentry, :l2, :l2_removed, :l2_nocommon, :l2_kfree, :l2_common, :l2_free, :l2_sub, :l2_one)
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
                prev = get(bystep, st - 1, nothing)
                (prev === nothing || st < 3) && continue
                for A in values(es), B in values(es)
                    A === B && continue
                    judge(A, B, prev, get(bystep, st - 2, nothing))
                end
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
