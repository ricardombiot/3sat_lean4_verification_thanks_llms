# Vía B del v208: ¿la estrella de una cima es cerrada dentro de una estructura de la unión? (29-sept-2026)
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_topstar.jl <salida.tsv> [muestras] [semilla]
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
        judge!(pin(u, [c]), k, "k_")
    end
    for _ in 1:SAMPLES
        p = rand(RNG[], (0.5, 0.7, 0.9))
        judge!(restrict(u, Set(x for x in alive(u) if rand(RNG[]) < p)), k, "r_")
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = Symbol[]
    for pre in ("r_", "k_"), c in ("pr_t", "pr_f", "fx_t", "fx_f", "tk_f", "yk_t", "yk_f")
        push!(cols, Symbol(pre, c))
    end
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
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
