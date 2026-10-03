# Lecturas completas (3-oct-2026, rama reader-stuck): ¿se atasca el lector? Como Lean `Reading`: desde cada estado
# final (revisado), fijar un nodo vivo y revisar, hasta tener fijado un nodo en cada paso. READ_N lecturas con orden
# de pasos y nodos al azar (semilla READ_SEED), y READ_N con los pasos en orden creciente y nodo al azar.
#   PROBE_MAP=bin PROBE_DIRS=../../lean/improves_bingo/scripts/cnf PROBE_ONLY=chain5_cross.cnf \
#     test_3sat/run_capped.sh 3500 6000 julia --heap-size-hint=3G --project=. test_3sat/probe_read_full.jl <salida.tsv>
#   rd_full / rd_stuck / rd_sat   lecturas / que dejan un estado inválido / cuyo resultado satisface la fórmula
#   (con prefijo rnd_ para el orden al azar y asc_ para el creciente)
using Random
const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
dump_partial() = open(OUT * ".partial", "w") do io
    for k in sort(collect(keys(C)), by = string)
        println(io, k, "\t", C[k])
    end
end
const READ_N = parse(Int, get(ENV, "READ_N", "200"))
const READ_SEED = parse(Int, get(ENV, "READ_SEED", "1"))

function reviewed(g)
    h = deepcopy(g); h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end
function pin(g, q)
    h = deepcopy(g); h.review_owners = true
    GraphPath.filter!(h, SetNodesId([q.id]))
    return h
end
alive_at(g, s) = collect(get(g.og.alive, Step(s), SetPathNodesId()))

# Una lectura completa: en el orden de pasos dado, fijar un nodo vivo al azar de cada paso. Devuelve el estado.
function read_one(g0, order, rng)
    g = g0
    for s in order
        g.is_valid || return g
        qs = alive_at(g, s)
        isempty(qs) && return g
        g = pin(g, qs[rand(rng, 1:length(qs))])
    end
    return g
end

# El resultado: el valor de cada variable en el paso de la variable (bin: paso 2v-1, índice 1 = cierto).
function check_sat(g, path)
    n = 0; cls = Vector{Vector{Int}}()
    for line in eachline(path)
        s = strip(line); (isempty(s) || s[1] in ('c', '%')) && continue
        if s[1] == 'p'; n = parse(Int, split(s)[3]); continue; end
        l = [parse(Int, t) for t in split(s) if t != "0"]; isempty(l) || push!(cls, l)
    end
    val = Dict{Int, Bool}()
    for v in 1:n
        qs = alive_at(g, 2v - 1)
        length(qs) == 1 || return false
        val[v] = first(qs).id.index == 1
    end
    return all(c -> any(l -> (l > 0) == val[abs(l)], c), cls)
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = [:rnd_full, :rnd_stuck, :rnd_sat, :asc_full, :asc_stuck, :asc_sat]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus()) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            if SatMachine.have_solution(machine)
                rng = MersenneTwister(READ_SEED)
                for g in SatMachine.get_gpath_solutions(machine)
                    g0 = reviewed(g)
                    top = Int(g0.current_step) - 1
                    for (pre, mk) in ((:rnd, () -> shuffle(rng, collect(1:top))), (:asc, () -> collect(1:top)))
                        for _ in 1:READ_N
                            h = read_one(g0, mk(), rng)
                            bump(Symbol(pre, :_full))
                            if !h.is_valid
                                bump(Symbol(pre, :_stuck))
                            elseif check_sat(h, path)
                                bump(Symbol(pre, :_sat))
                            end
                            dump_partial()
                        end
                    end
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
