# ¿Se cierra la familia fijada por color al bajar? (29-sept-2026, rama reader-stuck; sonda rápida): SideKeep.
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

function judge_branch!(V, u, pre)
    V.is_valid || return
    og = V.og; cs = Int(V.current_step)
    AV = alive(V)
    bump(Symbol(pre, "n"))
    firstmix = -1
    # nivel n (entrada con current_step n+1, cimas en el paso n): ¿V usa un solo valor en el paso n, y cabe en una entrada?
    for n in (cs - 3):-1:1
        vals = unique(z.id for z in AV if Int(z.id.step) == n)
        es = [E for ((key, st), E) in SENDER if st == n + 1]
        isempty(es) && continue
        if length(vals) >= 2
            firstmix < 0 && (firstmix = cs - 2 - n)
            continue
        end
        # un valor: ¿todas las aristas de V por debajo de n+1 están en la entrada de ese valor?
        E = get(SENDER, (vals[1], n + 1), nothing)
        E === nothing && continue
        ok = all(((a, b),) -> a == b || Int(a.id.step) > n || Int(b.id.step) > n || PG.has_edge(E.og, a, b), keys(og.edges))
        ok || bump(Symbol(pre, "oneval_notinE"))
    end
    if firstmix < 0
        bump(Symbol(pre, "never_mix"))
    else
        bump(Symbol(pre, "mix_d", min(firstmix, 4)))
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
    for c in cols
        judge_branch!(pin(u, [c]), u, "k_")
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = Symbol[]
    for pre in ("k_",), c in ("n", "never_mix", "mix_d1", "mix_d2", "mix_d3", "mix_d4", "oneval_notinE")
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
