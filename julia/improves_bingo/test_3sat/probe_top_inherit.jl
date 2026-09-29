# Herencia del paso libre de la estrella de un padre a la del hijo (29-sept-2026, rama reader-stuck; sonda rápida).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_top_inherit.jl <salida.tsv>
#
# En cada join u = e ∪ g, cima t (lado L, remitente SL, otro remitente SO), pareja ausente y–w de la estrella de t (de
# u, no de L, no de SL). Padres de t vivos en SL: P (1 o 2). Para cada padre q con y, w en su estrella (en SL):
# Fq = pasos libres (no extremos) en star_SL(q) con aristas de SL ∪ SO; Ft = pasos libres en star_u(t) con aristas de u.
#   abs; one_par (y, w en la estrella de un mismo padre); inh (algún paso de Fq está en Ft); inh_all (Fq ⊆ Ft);
#   split (ningún padre tiene a los dos); split_free (aun así Ft no vacío); two_par (t con dos padres);
#   en las repartidas, paso libre en ts-1 (padres), ts-2, ts-3 (sp_at_k, sp_at_k1, sp_at_k2), y sp_ids_k1: y y w no
#   comparten ningún id de testigo de la estrella en ts-2

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
const SENDER = Dict{Any, Any}()
const SIDES = Ref{Any}(nothing)

Core.eval(GraphPath, quote
    const _orig_up = do_up_filtering!
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        $(SENDER)[(map_id_node, gpath.map_parent_id, Int(gpath.current_step))] = (deepcopy(gpath), copy(requires))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

# el remitente de una llegada x: destino x.map_parent_id, clave = el color de x en el paso del remitente
function sender_of(x)
    k = Int(x.current_step) - 2
    k >= 0 || return nothing
    cols = unique(q.id for q in get(x.og.alive, k, SetPathNodesId()))
    length(cols) == 1 || return nothing
    return get(SENDER, (x.map_parent_id, first(cols), k + 1), nothing)
end

function on_join_post(u)
    e, g, se0, sg0 = SIDES[]; SIDES[] = nothing
    (se0 === nothing || sg0 === nothing) && (bump(:nosender); return)
    se, reqs = se0; sg = sg0[1]
    reqsteps = Set(Int(q.step) for q in reqs)
    u.current_step >= 2 || return
    og = u.og; top = u.current_step - 1
    Ae = alive(e)
    for t in get(og.alive, top, SetPathNodesId())
        ine = t in Ae
        L, SL, SO = ine ? (e, se, sg) : (g, sg, se)
        S = Set(z for z in alive(u) if PG.has_edge(og, z, t)); push!(S, t)
        tn = PathCollectionLines.get_node(L.table_lines, t)
        pars = tn === nothing ? PathNodeId[] : collect(tn.parents)
        for (y, w) in keys(og.edges)
            (y == w || !(y in S) || !(w in S) || PG.has_edge(L.og, y, w)) && continue
            bump(:np)
            PG.has_edge(SL.og, y, w) && continue
            bump(:abs)
            ps = [p for p in pars if PG.is_alive(SL.og, p)]
            length(ps) >= 2 && bump(:two_par)
            ends = (Int(y.id.step), Int(w.id.step))
            byl = Dict{Int, Vector{PathNodeId}}()
            for r in S
                push!(get!(byl, Int(r.id.step), PathNodeId[]), r)
            end
            Ft = Set(l for l in 0:top if !(l in ends) &&
                     all(r -> !(PG.has_edge(og, y, r) && PG.has_edge(og, w, r)), get(byl, l, PathNodeId[])))
            adj2(a, b) = PG.has_edge(SL.og, a, b) || PG.has_edge(SO.og, a, b)
            anyone = false; inh = false; inh_all = false
            for q in ps
                Sq = [z for (_, xs) in SL.og.alive for z in xs if PG.has_edge(SL.og, z, q)]
                (y in Sq && w in Sq) || continue
                anyone = true
                Fq = [l for l in 0:Int(SL.current_step)-1 if !(l in ends) &&
                      all(r -> r.id.step != l || !(adj2(y, r) && adj2(w, r)), Sq)]
                any(l -> l in Ft, Fq) && (inh = true)
                (!isempty(Fq) && all(l -> l in Ft, Fq)) && (inh_all = true)
            end
            if anyone
                bump(:one_par); inh && bump(:inh); inh_all && bump(:inh_all)
            else
                bump(:split); isempty(Ft) || bump(:split_free)
                ts = Int(t.id.step)
                (ts - 1) in Ft && bump(:sp_at_k)          # paso de los padres
                (ts - 2) in Ft && bump(:sp_at_k1)         # paso del padre de los padres
                (ts - 3) in Ft && bump(:sp_at_k2)         # paso del abuelo de los padres
                # ¿y solo posee, en el paso ts-2, nodos con el id del padre de un padre, y w con el del otro?
                idsY = Set(r.id for r in S if Int(r.id.step) == ts - 2 && PG.has_edge(og, y, r))
                idsW = Set(r.id for r in S if Int(r.id.step) == ts - 2 && PG.has_edge(og, w, r))
                isempty(intersect(idsY, idsW)) && bump(:sp_ids_k1)
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:nosender, :np, :abs, :two_par, :one_par, :inh, :inh_all, :split, :split_free, :sp_at_k, :sp_at_k1, :sp_at_k2, :sp_ids_k1)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDER)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b), sender_of(a), sender_of(b))),
                                 :join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
