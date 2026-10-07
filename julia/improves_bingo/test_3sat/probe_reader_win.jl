# El lector por nodos de ventana (7-oct-2026, rama reader-window; borrador drafts/path_win_reader.jl).
#
#   PROBE_MAP=bin PROBE_DIRS=../../lean/improves_bingo/scripts/cnf/tree PROBE_ONLY=tree3_pad.cnf \
#     test_3sat/run_capped.sh 3500 3600 julia --heap-size-hint=3G --project=. test_3sat/probe_reader_win.jl <salida.tsv>
#
# Con FORBID = :on (el modo de `runM .on` en Lean), desde cada estado final de la máquina, lecturas de ventanas (un
# filtro de tres ids y un review por ventana) en tres órdenes de cláusulas (natural, inverso y al azar):
#   finals                  estados finales de la máquina
#   det_n / det_ok / det_stuck / det_bad    primera elección: lecturas, solución, atasco, solución que no satisface
#   rnd_n / rnd_ok / rnd_stuck / rnd_bad    WIN_RND lecturas con elección al azar en cada paso (semilla WIN_SEED)
# `reader_winNode_tree` (ForbidOnPadLines.lean) predice det_stuck = det_bad = rnd_stuck = rnd_bad = 0 en la acolchada
# de todo árbol de cláusulas.
using Random
const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
include(joinpath(@__DIR__, "..", "drafts/path_win_reader.jl"))
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
dump_partial() = open(OUT * ".partial", "w") do io
    for k in sort(collect(keys(C)), by = string)
        println(io, k, "\t", C[k])
    end
end
const WIN_RND = parse(Int, get(ENV, "WIN_RND", "20"))
const WIN_SEED = parse(Int, get(ENV, "WIN_SEED", "1"))

function load_cnf(path)
    n = 0; cls = Vector{Vector{Int}}()
    for line in eachline(path)
        s = strip(line); (isempty(s) || s[1] in ('c', '%')) && continue
        if s[1] == 'p'; n = parse(Int, split(s)[3]); continue; end
        l = [parse(Int, t) for t in split(s) if t != "0"]; isempty(l) || push!(cls, l)
    end
    return n, cls
end
sat(sol, cls) = all(c -> any(l -> (l > 0) == sol[abs(l)], c), cls)

# Una lectura: :ok, :stuck (sin nodos vivos, inválido o variable sin fijar) o :bad (no satisface).
function one_read(g0, n, cls, order, choose)
    sol = try
        PathWinReader.read!(PathWinReader.new(deepcopy(g0), n, order); choose = choose)
    catch
        return :stuck
    end
    return sat(sol, cls) ? :ok : :bad
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = [:finals, :det_n, :det_ok, :det_stuck, :det_bad, :rnd_n, :rnd_ok, :rnd_stuck, :rnd_bad]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus()) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        n, cls = load_cnf(path)
        m = length(cls)
        rng = MersenneTwister(WIN_SEED)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            if SatMachine.have_solution(machine)
                for g0 in SatMachine.get_gpath_solutions(machine)
                    bump(:finals)
                    orders = [collect(1:m), collect(m:-1:1), shuffle(rng, collect(1:m))]
                    for order in orders
                        bump(:det_n)
                        bump(Symbol(:det_, one_read(g0, n, cls, order, first)))
                        for _ in 1:WIN_RND
                            bump(:rnd_n)
                            bump(Symbol(:rnd_, one_read(g0, n, cls, order, ids -> rand(rng, ids))))
                        end
                        dump_partial()
                    end
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
