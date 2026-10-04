# Tríos prohibidos en las aristas (FORBID, 30-sept-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,tseitin_petersen_H.cnf julia --project=. test_3sat/probe_forbid.jl <salida.tsv> [lecturas]
#
# Cada instancia se corre dos veces, con FORBID = :off y :on (con CHECK_OG: los invariantes del grafo, simetría de
# los tríos incluida, en cada review). Columnas:
#   sat_off, sat_on        — veredicto de la máquina (con :on nunca debe perder una SAT: la regla es sólida)
#   read_on                — el lector de siempre sobre el estado con :on lee una solución del exhaustivo
#   alive_off/on, edges_off/on — tamaño del primer estado final
#   trios_rule, edges_rule — tríos prohibidos y aristas cortadas por la regla en toda la corrida
#   trios_final            — tríos prohibidos guardados en el primer estado final
#   sp_runs, sp_stuck      — espina SIN revisión, elecciones al azar, estado :off, solo aristas
#   spf_runs, spf_stuck    — espina SIN revisión, elecciones al azar, estado :on, aristas y tríos prohibidos
#                            (el candidato r no puede formar trío prohibido con ninguna pareja ya elegida)
#   spf_bad                — lectura completa de spf que no es solución
#   secs_off, secs_on

using Random
const OUT = abspath(ARGS[1])
const RUNS = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 200
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(20260930))
const FIRST_LIT = get(ENV, "PROBE_MAP", "bin") == "bin" ? 1 : 0

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b || PG.has_edge(g.og, a, b)
nalive(g) = sum(length, values(g.og.alive); init = 0)

function bits_of(g, chosen)
    bits = Int[]; st = FIRST_LIT
    while haskey(chosen, st)
        nd = PathCollectionLines.get_node(g.table_lines, chosen[st])
        (nd === nothing || contains(nd.title, "or") || contains(nd.title, "FusionNode")) && break
        push!(bits, Int(chosen[st].id.index)); st += 2
    end
    return join(bits)
end

# La espina sin revisión: de la cima abajo, un candidato al azar vecino de todo lo elegido; con `trios`, además sin
# trío prohibido con ninguna pareja elegida.
function spine(g, rng; trios)
    top = Int(g.current_step) - 1
    chosen = Dict(top => rand(rng, alive_at(g, top)))
    for s in (top - 1):-1:0
        xs = collect(values(chosen))
        cands = [r for r in alive_at(g, s) if all(x -> adj(g, x, r), xs) &&
                 (!trios || !any(PG.dead_trio(g.og, xs[i], xs[j], r) for i in eachindex(xs) for j in i+1:length(xs)))]
        isempty(cands) && return nothing
        chosen[s] = rand(rng, cands)
    end
    return chosen
end

function run_machine(path, loader, mode)
    PG.FORBID[] = mode
    GraphPath.CHECK_OG[] = mode == :on ? :on : :off
    GraphPath.FORBID_TRIOS[] = 0; GraphPath.FORBID_EDGES[] = 0
    machine = SatMachine.new(loader(path))
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    return machine, t
end

function main()
    _, loader, first_lit = ProbeLib.map_of_env()
    header = "instance\ttruth\tsat_off\tsat_on\tread_on\talive_off\talive_on\tedges_off\tedges_on\ttrios_rule\t" *
             "edges_rule\ttrios_final\tsp_runs\tsp_stuck\tspf_runs\tspf_stuck\tspf_bad\tsecs_off\tsecs_on"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        m0, t0 = run_machine(path, loader, :off)
        m1, t1 = run_machine(path, loader, :on)
        trios_rule, edges_rule = GraphPath.FORBID_TRIOS[], GraphPath.FORBID_EDGES[]
        PG.FORBID[] = :off; GraphPath.CHECK_OG[] = :off
        s0, s1 = SatMachine.have_solution(m0), SatMachine.have_solution(m1)
        read_on = "-"; a0 = a1 = e0 = e1 = tf = "-"
        sp = spst = spf = spfst = spfbad = 0
        if s0
            g0 = first(SatMachine.get_gpath_solutions(m0))
            a0, e0 = nalive(g0), length(g0.og.edges)
            for _ in 1:RUNS
                sp += 1; spine(g0, RNG[]; trios = false) === nothing && (spst += 1)
            end
        end
        if s1
            g1 = first(SatMachine.get_gpath_solutions(m1))
            a1, e1 = nalive(g1), length(g1.og.edges)
            tf = sum(e -> length(e.forbid), values(g1.og.edges); init = 0) ÷ 3
            PG.FORBID[] = :on                        # el lector revisa con la regla
            r = PathReader.new(deepcopy(g1), first_lit)
            PathReader.read!(r)
            PG.FORBID[] = :off
            read_on = ex === nothing ? "?" : string(join(Int.(r.solution)) in ex)
            for _ in 1:RUNS
                spf += 1
                ch = spine(g1, RNG[]; trios = true)
                if ch === nothing
                    spfst += 1
                elseif ex !== nothing && !(bits_of(g1, ch) in ex)
                    spfbad += 1
                end
            end
        end
        return (truth, s0, s1, read_on, a0, a1, e0, e1, trios_rule, edges_rule, tf, sp, spst, spf, spfst, spfbad,
                round(t0, digits = 1), round(t1, digits = 1))
    end
end

main()
