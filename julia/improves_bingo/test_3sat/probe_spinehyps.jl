# Las hipótesis de readerVerdict_iff_of_spine en los estados que visita el lector (30-sept-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_spinehyps.jl <salida.tsv> [secuencias]
#
# Desde el estado final (revisado), secuencias de fijaciones de color al azar (como Visited: cualquier pin en cualquier
# paso), y en cada estado válido:
#   twopar_max — máximo de padres vivos poseídos de un nodo vivo (TwoParents: ≤ 2);
#   spine      — la espina desde CADA cima, eligiendo al azar entre los padres vivos poseídos vecinos de toda la
#                cadena; stuck = se quedó sin candidato (SpineTrio falla en esa cadena).

using Random
const OUT = abspath(ARGS[1])
const SEQS = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 6
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20260930))

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
allalive(g) = [x for (_, xs) in g.og.alive for x in xs]

function live_parents(g, x)
    nd = PathCollectionLines.get_node(g.table_lines, x)
    nd === nothing && return PathNodeId[]
    [p for p in nd.parents if PG.is_alive(g.og, p) && PG.has_edge(g.og, x, p)]
end

const NPINS = Ref(0)
function spine_any(g, chain, x, s)
    s < 0 && return true
    for p in [p for p in live_parents(g, x) if all(w -> w == p || PG.has_edge(g.og, w, p), chain)]
        spine_any(g, vcat(chain, [p]), p, s - 1) && return true
    end
    return false
end
function pin_node!(g, p)
    for y in alive_at(g, Int(p.id.step))
        y == p && continue
        GraphPath.remove_node_owner!(g, y; rule = :probe)
        g.is_valid || return g
    end
    g.review_owners = true
    g.is_valid && GraphPath.filter!(g, SetNodesId())
    return g
end
# el lector por caminos CON revisión tras cada fijación, eligiendo el padre al azar
function path_review(g0, t)
    top = Int(g0.current_step) - 1
    g = pin_node!(deepcopy(g0), t)
    g.is_valid || return (false, 0)
    x = t; choices = 0
    for s in (top - 1):-1:0
        cands = live_parents(g, x)
        isempty(cands) && return (false, choices)
        length(cands) >= 2 && (choices += 1)
        p = cands[rand(RNG[], 1:length(cands))]
        g = pin_node!(g, p)
        (g.is_valid && PG.is_alive(g.og, x)) || return (false, choices)
        x = p
    end
    return (true, choices)
end
function judge(g)
    g.is_valid || return
    bump(:states)
    top = Int(g.current_step) - 1
    m = 0
    for x in allalive(g)
        m = max(m, length(live_parents(g, x)))
    end
    C[:twopar_max] = max(get(C, :twopar_max, 0), m)
    m > 2 && bump(:twopar_fail)
    for t in alive_at(g, top)
        chain = [t]; x = t; ok = true; choices = 0; stuckat = -1
        for s in (top - 1):-1:0
            cands = [p for p in live_parents(g, x) if all(w -> w == p || PG.has_edge(g.og, w, p), chain)]
            isempty(cands) && (ok = false; stuckat = s; break)
            length(cands) >= 2 && (bump(:two_cands); choices += 1)
            p = cands[rand(RNG[], 1:length(cands))]
            push!(chain, p); x = p
        end
        bump(:spines); ok || bump(:stuck)
        for _ in 1:3
            (okr, ch) = path_review(g, t)
            bump(:rev_runs); bump(:rev_choices, ch); okr || bump(:rev_stuck)
        end
        if !ok
            anyok = spine_any(g, [t], t, top - 1)
            println(stderr, "STUCK pins=", NPINS[], " top=", t, " at_step=", stuckat, " of ", top,
                    " prior_choices=", choices, " other_choices_ok=", anyok,
                    " n_tops=", length(alive_at(g, top)), " live_parents_last=", length(live_parents(g, x)))
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:states, :twopar_max, :twopar_fail, :spines, :two_cands, :stuck, :rev_runs, :rev_choices, :rev_stuck)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            if SatMachine.have_solution(machine)
                for g0 in SatMachine.get_gpath_solutions(machine)
                    NPINS[] = 0; judge(g0)
                    for _ in 1:SEQS
                        g = deepcopy(g0); NPINS[] = 0
                        steps = shuffle(RNG[], collect(0:Int(g.current_step) - 1))
                        for st in steps
                            ids = unique(x.id for x in alive_at(g, st))
                            length(ids) >= 2 || continue
                            GraphPath.filter!(g, SetNodesId([ids[rand(RNG[], 1:length(ids))]]))
                            g.is_valid || break
                            NPINS[] += 1; judge(g)
                        end
                    end
                end
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
