# SibStarInv y el primer pin (30-sept-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_sibstar.jl <salida.tsv> [muestras]
#
# Sobre cada entrada de la línea (copia del remitente antes del filtro) y cada estado final:
#   sib_*   — estructuras cerradas cuyas cimas son hermanas (las de una llegada: mismo id y padre), obtenidas quitando
#             las demás cimas (y un subconjunto al azar) y revisando; para cada cima t y la estrella de t: restringir
#             a la estrella y revisar, ¿conserva todos los nodos y las aristas a t? (SibStarInv)
#   whole_* — el estado entero restringido a la estrella de cada cima (el primer pin del lector por caminos).

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 3
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20260930))
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

alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
function restrict(g, U)
    h = deepcopy(g)
    for x in collect(alive(h))
        x in U && continue
        GraphPath.remove_node_owner!(h, x; rule = :probe)
        h.is_valid || return h
    end
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

# para cada cima t de V: restringir a la estrella y revisar; ¿quedan todos los nodos y las aristas a t?
function star_check(V, pre)
    V.is_valid || return
    top = Int(V.current_step) - 1
    for t in alive_at(V, top)
        S = Set(z for z in alive(V) if z == t || PG.has_edge(V.og, z, t))
        W = restrict(V, S)
        bump(Symbol(pre, "_t"))
        if !W.is_valid
            bump(Symbol(pre, "_inval")); continue
        end
        AW = alive(W)
        issubset(S, AW) || bump(Symbol(pre, "_lostnode"))
        # testigos fuera de la estrella en las parejas cortadas
        if pre == "sib" || pre == "sibr"
            others = [q for q in alive_at(V, top) if q != t]
            nd = PathCollectionLines.get_node(V.table_lines, t)
            pars = nd === nothing ? PathNodeId[] : [p for p in nd.parents if PG.is_alive(V.og, p) && PG.has_edge(V.og, t, p)]
            for (a, b) in keys(V.og.edges)
                (a == b || !(a in S) || !(b in S) || a == t || b == t) && continue
                PG.has_edge(W.og, a, b) && continue
                bump(Symbol(pre, "_cut"))
                for l in 0:top-1
                    wit = [r for r in alive_at(V, l) if (r == a || PG.has_edge(V.og, a, r)) && (r == b || PG.has_edge(V.og, b, r))]
                    any(r -> r in S, wit) && continue
                    for r in wit
                        bump(Symbol(pre, "_w"))
                        any(p -> r == p || PG.has_edge(V.og, r, p), pars) ? bump(Symbol(pre, "_w_parown")) : bump(Symbol(pre, "_w_noparown"))
                        any(q -> PG.has_edge(V.og, r, q), others) && bump(Symbol(pre, "_w_instar2"))
                        # color del abuelo de t: ¿r posee algún nodo de ese color en el paso del abuelo?
                        if t.gparent_id !== nothing
                            gp = t.gparent_id
                            gpl = Int(gp.step)
                            hasgp = any(q -> q.id == gp && (q == r || PG.has_edge(V.og, r, q)), alive_at(V, gpl))
                            hasgp || bump(Symbol(pre, "_w_nogp"))
                        end
                    end
                    break
                end
            end
        end
        all(z -> z == t || (z in AW && PG.has_edge(W.og, z, t)), S) || bump(Symbol(pre, "_lostedge"))
    end
end

function judge_entry(g)
    g.is_valid || return
    bump(:entries)
    star_check(g, "whole")
    top = Int(g.current_step) - 1
    tops = alive_at(g, top)
    groups = unique((q.id, q.parent_id) for q in tops)
    length(groups) >= 2 && bump(:multigroup)
    for G in groups
        keep = Set(x for x in alive(g) if !(Int(x.id.step) == top && (x.id, x.parent_id) != G))
        ntop = count(q -> (q.id, q.parent_id) == G, tops)
        ntop >= 2 && bump(:sib_two)
        V = restrict(g, keep)
        star_check(V, "sib")
        for _ in 1:SAMPLES
            p = rand(RNG[], (0.6, 0.8, 0.95))
            star_check(restrict(g, Set(x for x in keep if rand(RNG[]) < p)), "sibr")
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:entries, :multigroup, :sib_two, :whole_t, :whole_inval, :whole_lostnode, :whole_lostedge,
            :sib_t, :sib_inval, :sib_lostnode, :sib_lostedge, :sib_cut, :sib_w, :sib_w_parown, :sib_w_noparown, :sib_w_instar2, :sib_w_nogp, :sibr_t, :sibr_inval, :sibr_lostnode, :sibr_lostedge, :sibr_cut, :sibr_w, :sibr_w_parown, :sibr_w_noparown, :sibr_w_instar2, :sibr_w_nogp,
            :final_t, :final_inval, :final_lostnode, :final_lostedge)
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
            for (_, g) in SENDER
                Int(g.current_step) >= 2 && judge_entry(g)
            end
            if SatMachine.have_solution(machine)
                for g0 in SatMachine.get_gpath_solutions(machine)
                    star_check(g0, "final")
                end
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
