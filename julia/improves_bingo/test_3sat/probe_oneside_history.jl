# StarOneSide por la historia (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_oneside_history.jl <salida.tsv>
#
# Se guarda el remitente de cada llegada (copia antes del filtro). En cada join u = e ∪ g y cada cima t (lado L,
# remitente SL), para cada pareja y–w de la estrella de t que es de u y no de L:
#   removed — la pareja era arista de SL (la quitó la llegada: filtro o review); rm_gap: tras la llegada, L no tiene
#             testigo común en algún paso interior (regla de parejas); rm_gap_kept: alguno de esos pasos sigue libre en
#             la estrella de t en u; rm_nogap: L tiene testigo en todo paso (la quitó otra regla); rm_nogap_ok: aun así
#             hay paso libre en la estrella; rm_nf: sin paso libre en la estrella (StarOneSide fallaría);
#             gap_steps: pasos-hueco de L; gap_cross: de ellos, con algún r de la estrella unido a y o a w por una arista
#             de fuera de L; gap_wit: con algún r de la estrella testigo común en u; free_/fill_req|noreq: pasos-hueco
#             que siguen libres / que se tapan en u, según sean o no pasos con requisito del destino. En los que siguen
#             libres, los testigos de y–w en la otra llegada O: gw_none (ninguno), gw_all_dead_in_L (todos muertos en L),
#             gw_alive_not_star (alguno vivo en L fuera de la estrella), gw_all_in_SL (todos vivos en el remitente SL)
#   absent  — no lo era; ab_star: y y w están en la estrella (en SL) de algún padre de t; ab_free: y en SL ∪ SO (SO el
#             remitente del otro lado) la pareja ya tenía un paso sin testigo en esa estrella (la inducción serviría);
#             npar1/2/3: padres vivos de t (3 = 3 o más); gr_star / gr_free: lo mismo con la estrella del grupo de padres

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
            if PG.has_edge(SL.og, y, w)
                bump(:removed)
                ends = (Int(y.id.step), Int(w.id.step))
                stepsI = [l for l in 0:u.current_step-1 if !(l in ends)]
                wit(o, l, pool) = any(r -> r.id.step == l && PG.has_edge(o, y, r) && PG.has_edge(o, w, r), pool)
                AL = [z for (_, xs) in L.og.alive for z in xs]
                efree = [l for l in stepsI if !wit(L.og, l, AL)]          # sin testigo en todo L (regla de parejas)
                ufree = [l for l in stepsI if !wit(og, l, S)]             # sin testigo en la estrella de t, en u
                isempty(efree) ? bump(:rm_nogap) : bump(:rm_gap)          # rm_nogap: la quitó otra regla (pasadas)
                any(l -> l in ufree, efree) && bump(:rm_gap_kept)         # el hueco de L sigue en la estrella en u
                # en los pasos-hueco de L: ¿hay nodos r de la estrella con una arista de fuera de L hacia y o hacia w?
                for l in efree
                    (l in ufree) && bump(l in reqsteps ? :free_req : :free_noreq)
                    if l in ufree
                        # los testigos de y–w en la otra llegada O en ese paso
                        O = ine ? g : e
                        AO = [z for (_, xs) in O.og.alive for z in xs]
                        AL2 = Set(AL)
                        gw = [r for r in AO if r.id.step == l && PG.has_edge(O.og, y, r) && PG.has_edge(O.og, w, r)]
                        isempty(gw) && bump(:gw_none)
                        all(r -> !(r in AL2), gw) && !isempty(gw) && bump(:gw_all_dead_in_L)
                        any(r -> (r in AL2) && !PG.has_edge(og, t, r), gw) && bump(:gw_alive_not_star)
                        # ¿estaban vivos en el remitente SL?
                        all(r -> PG.is_alive(SL.og, r), gw) && !isempty(gw) && bump(:gw_all_in_SL)
                    end
                    (l in ufree) || bump(l in reqsteps ? :fill_req : :fill_noreq)
                    rs = [r for r in S if r.id.step == l]
                    cross = count(r -> (PG.has_edge(og, y, r) && !PG.has_edge(L.og, y, r)) ||
                                       (PG.has_edge(og, w, r) && !PG.has_edge(L.og, w, r)), rs)
                    bump(:gap_steps)
                    cross > 0 && bump(:gap_cross)
                    # con arista cruzada a uno y arista (de L o no) al otro: casi testigo
                    half = count(r -> (PG.has_edge(og, y, r) && PG.has_edge(og, w, r)), rs)
                    half > 0 && bump(:gap_wit)
                end
                isempty(ufree) && bump(:rm_nf)                            # (StarOneSide fallaría)
                # si no hay hueco en L: ¿el paso libre en u es uno donde L solo tiene testigos fuera de la estrella?
                if isempty(efree) && !isempty(ufree)
                    bump(:rm_nogap_ok)
                end
            else
                bump(:absent)
                # el grupo de padres de t (vivos en SL): la unión de sus estrellas, aristas de SL ∪ SO
                ps = [p for p in pars if PG.is_alive(SL.og, p)]
                bump(Symbol("npar", min(length(ps), 3)))
                adjG(a, b) = PG.has_edge(SL.og, a, b) || PG.has_edge(SO.og, a, b)
                SG = Set(z for (_, xs) in SL.og.alive for z in xs if any(p -> PG.has_edge(SL.og, z, p), ps))
                if y in SG && w in SG
                    bump(:gr_star)
                    gfree = any(l -> !(l == y.id.step || l == w.id.step) &&
                                     all(r -> r.id.step != l || !(adjG(y, r) && adjG(w, r)), SG), 0:SL.current_step-1)
                    gfree && bump(:gr_free)
                end
                # en el paso anterior: estrella de un padre p de t en SL, aristas de SL ∪ SO
                for p in pars
                    (PG.is_alive(SL.og, p) && PG.has_edge(SL.og, p, y) && PG.has_edge(SL.og, p, w)) || continue
                    bump(:ab_star)
                    Sp = [z for (_, xs) in SL.og.alive for z in xs if PG.has_edge(SL.og, z, p)]
                    adj(a, b) = PG.has_edge(SL.og, a, b) || PG.has_edge(SO.og, a, b)
                    free = any(l -> !(l == y.id.step || l == w.id.step) &&
                                    all(r -> r.id.step != l || !(adj(y, r) && adj(w, r)), Sp), 0:SL.current_step-1)
                    free && bump(:ab_free)
                    break
                end
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:nosender, :np, :removed, :rm_gap, :rm_gap_kept, :rm_nogap, :rm_nogap_ok, :rm_nf, :gap_steps, :gap_cross, :gap_wit, :free_req, :free_noreq, :fill_req, :fill_noreq, :gw_none, :gw_all_dead_in_L, :gw_alive_not_star, :gw_all_in_SL, :absent, :ab_star, :ab_free, :npar1, :npar2, :npar3, :gr_star, :gr_free)
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
