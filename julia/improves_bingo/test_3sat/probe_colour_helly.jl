# Helly dentro de cada clase de color (29-sept-2026, rama reader-stuck; Lean `SepLine.lean`, SplitSat2).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_colour_helly.jl <salida.tsv> [muestras] [semilla]
#
# En cada join (paso del remitente k = T - 2, colores a y s), para P = [] y `muestras` P al azar, si h = pin(unión, P)
# es válido: para cada color c, la clase K_c (vivos de h en k con id c) y, para cada vivo y, W_c(y) = testigos de c que
# posee (K_c ∩ vecinos de y). Se cuentan los triángulos de h (y, w, z vivos que se poseen dos a dos, distintos) con
# W_c dos a dos no disjuntos pero sin punto común: helly_fail (por color). Si no hay, la estructura del color c
# (parejas con testigo común de c) cumple la regla de parejas por Helly local.
# Por instancia: states, class_max (tamaño máximo de una clase), size1..size4+ (clases por tamaño), tri (triángulos
# con W dos a dos no disjuntos, por color), helly_fail, states_fail (estados con algún fallo).

using Random

const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 5
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)
pin(g, P) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(P)); g2)

const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(SEED))

function judge!(h, k, cols)
    og = h.og
    V = [x for (_, xs) in og.alive for x in xs]
    nV = length(V)
    idx = Dict(x => i for (i, x) in enumerate(V))
    adj = [Int[] for _ in 1:nV]
    for (y, w) in keys(og.edges)
        (y == w || !haskey(idx, y) || !haskey(idx, w)) && continue
        push!(adj[idx[y]], idx[w]); push!(adj[idx[w]], idx[y])
    end
    nbr = [Set(a) for a in adj]
    fail = false
    for c in cols
        K = [x for x in get(og.alive, k, SetPathNodesId()) if x.id == c]
        n = length(K)
        n == 0 && continue
        bump(n >= 4 ? :size4p : Symbol("size$n"))
        C[:class_max] = max(get(C, :class_max, 0), n)
        W = zeros(UInt8, nV)
        for i in 1:nV, (j, r) in enumerate(K)
            PG.has_edge(og, V[i], r) && (W[i] |= UInt8(1) << (j - 1))
        end
        for i in 1:nV, j in adj[i]
            j > i || continue
            (W[i] & W[j]) == 0 && continue
            for l in adj[j]
                l > j || continue
                l in nbr[i] || continue
                ((W[i] & W[l]) == 0 || (W[j] & W[l]) == 0) && continue
                bump(:tri)
                if (W[i] & W[j] & W[l]) == 0
                    bump(:helly_fail); fail = true
                end
            end
        end
    end
    fail && bump(:states_fail)
end

function on_join_post(u)
    k = u.current_step - 2
    k >= 0 || return
    cols = map_nodes(u.og, k)
    length(cols) == 2 || return
    steps = choice_steps(u.og)
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(2, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(u.og, kk)) for kk in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps
        h = pin(u, P)
        h.is_valid || continue
        bump(:states)
        judge!(h, k, cols)
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:states, :class_max, :size1, :size2, :size3, :size4p, :tri, :helly_fail, :states_fail)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
