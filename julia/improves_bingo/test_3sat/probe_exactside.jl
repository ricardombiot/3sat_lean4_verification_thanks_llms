# Fijar un color dentro de una estructura de la unión, ¿mata exactamente lo que no es de ese lado? (29-sept-2026)
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_exactside.jl <salida.tsv> [muestras] [semilla]
#
# Estructuras cerradas al azar V de la unión (restringir a un subconjunto al azar de vivos y revisar, como
# probe_secin.jl). Para cada color c del paso del remitente, con su lado L (e para el color de e, g para el de g):
#   ex_t / ex_f — los vivos de pin(V, c) son exactamente V ∩ vivos(L) (o ex_f: no)
#   lost        — nodos de V ∩ vivos(L) que mueren al fijar c
#   extra       — vivos de pin(V, c) fuera de L (no debería haber: alive_side)
#   w_t / w_f   — los vivos de pin(V, c) son exactamente los de V con un testigo de color c en k dentro de V
#   w_lost / w_extra — de esos, los que mueren / supervivientes sin ese testigo
#   e_t / e_f   — las aristas de pin(V, c) son exactamente las de V entre esos nodos con testigo común de color c en k
#   e_lost / e_extra — de esas, las que se cortan / aristas que quedan sin testigo común
#   nc_f        — nodos de V que no sobreviven a fijar ningún color (NodeColour)

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

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

const SIDES = Ref{Any}(nothing)
function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    k = u.current_step - 2
    k >= 0 || return
    ca = unique(x.id for x in get(e.og.alive, k, SetPathNodesId()))
    cs = unique(x.id for x in get(g.og.alive, k, SetPathNodesId()))
    (length(ca) == 1 && length(cs) == 1) || return
    for _ in 1:SAMPLES
        p = rand(RNG[], (0.5, 0.7, 0.9))
        V = restrict(u, Set(x for x in alive(u) if rand(RNG[]) < p))
        V.is_valid || continue
        AV = alive(V)
        surv = Set{PathNodeId}()
        for (c, L) in ((ca[1], e), (cs[1], g))
            h = pin(V, [c])
            A = h.is_valid ? alive(h) : Set{PathNodeId}()
            union!(surv, A)
            want = intersect(AV, alive(L))
            bump(:ex_t)
            A == want || bump(:ex_f)
            bump(:lost, length(setdiff(want, A)))
            bump(:extra, length(setdiff(A, alive(L))))
            # candidato por testigo: sobreviven los de V con un testigo de color c en el paso k dentro de V
            Kc = [r for r in get(V.og.alive, k, SetPathNodesId()) if r.id == c]
            Wc = Set(y for y in AV if any(r -> PathOwnersGraph.has_edge(V.og, y, r), Kc))
            bump(:w_t)
            A == Wc || bump(:w_f)
            bump(:w_lost, length(setdiff(Wc, A)))
            bump(:w_extra, length(setdiff(A, Wc)))
            # aristas: las de V con un testigo común de color c en k dentro de V
            if h.is_valid
                Ec = Set((y, w) for (y, w) in keys(V.og.edges) if y in Wc && w in Wc &&
                         any(r -> PathOwnersGraph.has_edge(V.og, y, r) && PathOwnersGraph.has_edge(V.og, w, r), Kc))
                Eh = Set(keys(h.og.edges))
                bump(:e_t)
                Eh == Ec || bump(:e_f)
                bump(:e_lost, length(setdiff(Ec, Eh)))
                bump(:e_extra, length(setdiff(Eh, Ec)))
            end
        end
        bump(:nodes, length(AV))
        bump(:nc_f, length(setdiff(AV, surv)))
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:ex_t, :ex_f, :lost, :extra, :nodes, :nc_f, :w_t, :w_f, :w_lost, :w_extra, :e_t, :e_f, :e_lost, :e_extra)
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
