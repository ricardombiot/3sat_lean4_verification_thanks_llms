# SecSplit en los joins (29-sept-2026, rama reader-stuck; Lean `SecExactLine.lean`).
#
#   PROBE_MAP=bin PAIRS=200 PROBE_LIMIT=N julia --project=. test_3sat/probe_secsplit.jl <salida.tsv> [muestras_3] [semilla]
#
# SecSplit e g: una estructura cerrada no vacía de la unión que concuerda con P da una en algún lado. Con el review
# cerrado, «hay estructura cerrada no vacía que concuerda con P» es «fijar P deja el estado válido»
# (pinEdge_iff_kernel), así que se mide en su forma de pins:
#   pin(unión, P) válido  ⟹  pin(e, P) válido  ∨  pin(g, P) válido
# En cada join de la máquina (puntos :join_pre / :join_post), con P de nodos de mapa de pasos con elección de la
# unión: todos los P de 1 nodo, todos los de 2 (pasos distintos; con PAIRS=N, N al azar) y `muestras_3` P de 3 al azar.
# Por instancia: joins, tests (P con la unión válida), fails (unión válida, los dos lados inválidos), por tamaño
# (t1 f1 t2 f2 t3 f3), y dead (P con la unión inválida). Las crafted van primero.

using Random

const OUT = abspath(ARGS[1])
const SAMPLES3 = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929
# PAIRS=N: N pares al azar por join en lugar de todos (0 = todos).
const PAIRS = parse(Int, get(ENV, "PAIRS", "0"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in og.alive[k]), by = n -> n.index)
valid_pin(g, P) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(P)); g2.is_valid)

mutable struct Acc
    joins :: Int; dead :: Int
    t :: Vector{Int}; f :: Vector{Int}
end
const ACC = Ref{Acc}()
const SIDES = Ref{Any}(nothing)
const RNG = Ref(MersenneTwister(SEED))

function test!(u, e, g, P)
    a = ACC[]; n = length(P)
    if !valid_pin(u, P)
        a.dead += 1
        return
    end
    a.t[n] += 1
    (valid_pin(e, P) || valid_pin(g, P)) || (a.f[n] += 1)
end

function on_join_post(u)
    e, g = SIDES[]
    SIDES[] = nothing
    ACC[].joins += 1
    steps = choice_steps(u.og)
    nodes = Dict(k => map_nodes(u.og, k) for k in steps)
    for k in steps, b in nodes[k]
        test!(u, e, g, [b])
    end
    if PAIRS == 0
        for (i, k1) in enumerate(steps), k2 in steps[i+1:end], b1 in nodes[k1], b2 in nodes[k2]
            test!(u, e, g, [b1, b2])
        end
    elseif length(steps) >= 2
        for _ in 1:PAIRS
            k1, k2 = shuffle(RNG[], steps)[1:2]
            test!(u, e, g, [rand(RNG[], nodes[k1]), rand(RNG[], nodes[k2])])
        end
    end
    if length(steps) >= 3
        for _ in 1:SAMPLES3
            ks = shuffle(RNG[], steps)[1:3]
            test!(u, e, g, [rand(RNG[], nodes[k]) for k in ks])
        end
    end
end

function run_one(path, loader)
    ACC[] = Acc(0, 0, zeros(Int, 3), zeros(Int, 3))
    machine = SatMachine.new(loader(path))
    Probes.with(:join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b))), :join_post => on_join_post) do
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
    end
    return ACC[]
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    header = "instance\ttruth\tjoins\ttests\tfails\tt1\tf1\tt2\tf2\tt3\tf3\tdead\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        t = @elapsed a = run_one(path, loader)
        return (truth, a.joins, sum(a.t), sum(a.f), a.t[1], a.f[1], a.t[2], a.f[2], a.t[3], a.f[3], a.dead,
                round(t, digits = 1))
    end
end

main()
