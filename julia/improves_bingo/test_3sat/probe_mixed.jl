# Estructuras mixtas en los joins (29-sept-2026, rama reader-stuck; Lean `SepLine.lean`, SplitSat2).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_mixed.jl <salida.tsv> [muestras] [semilla]
#
# En el mapa bin cada join une dos lados de un color cada uno en el paso del remitente k = T - 2 (joinProv_two).
# SplitSat2 pregunta si una estructura cerrada de la unión puede necesitar testigos de los dos colores en k. En cada
# join, para P = [] y `muestras` P al azar (1 o 2 nodos del mapa de pasos con elección), si h = pin(unión, P) es válido:
#   nodos del paso k por color (cuántos nodos de camino agrupa cada color),
#   para cada arista (y, w) de h, el conjunto de colores de sus testigos en k (r vivo en k con y–r y w–r):
#     only_a / only_s / both — aristas con testigos de un solo color o de los dos,
#   mixed: h tiene a la vez aristas only_a y only_s,
#   pa / ps: pin(h, a) / pin(h, s) válido; split_fail: ninguno de los dos (fallo de SplitSat2).
# Por instancia: joins, states (h juzgados), nodes_k (media de nodos de camino por color), e_only_a, e_only_s, e_both,
# mixed, mixed_pa, mixed_ps, mixed_both (los dos pins válidos en estados mixtos), split_fail.

using Random

const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 10
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
const NODES = Ref(0.0); const NODES_N = Ref(0)
const RNG = Ref(MersenneTwister(SEED))

function judge!(h, k, a, s)
    og = h.og
    wit = collect(get(og.alive, k, SetPathNodesId()))
    ea = 0; es = 0
    for (y, w) in keys(og.edges)
        cols = Set(r.id for r in wit if PG.has_edge(og, y, r) && PG.has_edge(og, w, r))
        if cols == Set([a]); ea += 1
        elseif cols == Set([s]); es += 1
        elseif a in cols && s in cols; bump(:e_both)
        end
    end
    bump(:e_only_a, ea); bump(:e_only_s, es)
    pa = pin(h, [a]).is_valid; ps = pin(h, [s]).is_valid
    (pa || ps) || bump(:split_fail)
    if ea > 0 && es > 0
        bump(:mixed)
        pa && bump(:mixed_pa); ps && bump(:mixed_ps); (pa && ps) && bump(:mixed_both)
    end
end

function on_join_post(u)
    bump(:joins)
    k = u.current_step - 2
    k >= 0 || return
    cols = map_nodes(u.og, k)
    length(cols) == 2 || return
    a, s = cols
    for c in cols
        NODES[] += count(x -> x.id == c, get(u.og.alive, k, SetPathNodesId())); NODES_N[] += 1
    end
    steps = choice_steps(u.og)
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(2, length(steps)))
            ks = shuffle(RNG[], steps)[1:m]
            push!(Ps, [rand(RNG[], map_nodes(u.og, kk)) for kk in ks])
        end
    end
    for P in Ps
        h = pin(u, P)
        h.is_valid || continue
        bump(:states)
        judge!(h, k, a, s)
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :states, :e_only_a, :e_only_s, :e_both, :mixed, :mixed_pa, :mixed_ps, :mixed_both, :split_fail)
    header = "instance\ttruth\tnodes_k\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); NODES[] = 0; NODES_N[] = 0
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, NODES_N[] == 0 ? 0 : round(NODES[] / NODES_N[], digits = 1), (get(C, c, 0) for c in cols)...,
                round(t, digits = 1))
    end
end

main()
