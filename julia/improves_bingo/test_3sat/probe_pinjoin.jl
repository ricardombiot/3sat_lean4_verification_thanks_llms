# Filtro y join conmutan? (30-sept-2026, rama reader-stuck; PinStableF en el join)
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_pinjoin.jl <salida.tsv> [muestras]
#
# Con FORBID = :on. En cada join (:join_pre / :join_post), para pins R al azar (1-3 nodos de mapa por debajo de la
# cima): U' = pin(join(A,B), R) frente a J = join(pin(A,R), pin(B,R)) (pin = filter! con revisión).
#   runs, valid_diff, alive_UJ (vivos de U' que no están en J), alive_JU, edge_UJ, edge_JU

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 4
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20260930))
const PRE = Ref{Any}(nothing)
alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
allalive(g) = Set(x for (_, xs) in g.og.alive for x in xs)

function random_pins(g, n)
    top = Int(g.current_step) - 1
    steps = [s for s in 1:top-1 if length(unique(x.id for x in alive_at(g, s))) >= 2]
    isempty(steps) && return NodeId[]
    [begin ids = unique(x.id for x in alive_at(g, s)); ids[rand(RNG[], 1:length(ids))] end
     for s in shuffle(RNG[], steps)[1:min(n, length(steps))]]
end
pin(g, R) = (h = deepcopy(g); h.review_owners = true; GraphPath.filter!(h, SetNodesId(R)); h)

function judge(u, a, b)
    u.is_valid || return
    for _ in 1:SAMPLES
        R = random_pins(u, rand(RNG[], 1:3))
        isempty(R) && continue
        bump(:runs)
        U = pin(u, R)
        pa, pb = pin(a, R), pin(b, R)
        J = if pa.is_valid && pb.is_valid
            j = deepcopy(pa); GraphPath.do_join!(j, pb); j
        elseif pa.is_valid; pa elseif pb.is_valid; pb else nothing end
        vU = U.is_valid; vJ = J !== nothing && J.is_valid
        vU != vJ && (bump(:valid_diff); continue)
        vU || continue
        AU, AJ = allalive(U), allalive(J)
        isempty(setdiff(AU, AJ)) || bump(:alive_UJ)
        isempty(setdiff(AJ, AU)) || bump(:alive_JU)
        EU, EJ = Set(keys(U.og.edges)), Set(keys(J.og.edges))
        isempty(setdiff(EU, EJ)) || bump(:edge_UJ)
        isempty(setdiff(EJ, EU)) || bump(:edge_JU)
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:runs, :valid_diff, :alive_UJ, :alive_JU, :edge_UJ, :edge_JU)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            Probes.with(:join_pre => (a, b) -> (PRE[] = (deepcopy(a), deepcopy(b))),
                        :join_post => u -> (PRE[] === nothing || judge(deepcopy(u), PRE[]...); PRE[] = nothing)) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
