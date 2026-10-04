# Tiempo de la máquina con FORBID = :off y :on (30-sept-2026, rama reader-stuck).
#
#   test_3sat/run_capped.sh 4000 <tope_s> julia --heap-size-hint=3G --project=. test_3sat/probe_forbid_time.jl \
#       <instancia.cnf> <off|on> <salida.tsv>
#
# Una instancia y un modo por proceso (así run_capped corta por memoria o tiempo sin perder las demás). Calienta con
# una instancia mínima en el mismo modo y añade una línea a la salida:
#   instance  mode  vars  clauses  verdict  secs  trios_rule  edges_rule  rounds

const PATH = abspath(ARGS[1])
const MODE = Symbol(ARGS[2])
const OUT = abspath(ARGS[3])
include(joinpath(@__DIR__, "..", "src/main.jl"))
const PG = PathOwnersGraph

function run_once(path)
    machine = SatMachine.new(GraphMapBin.load_import_bin!(path))
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    return machine, t
end

PG.FORBID[] = MODE
run_once(joinpath(@__DIR__, "..", "test/example_cnf/bin_v3_c2.cnf"))      # calentar
GraphPath.FORBID_TRIOS[] = 0; GraphPath.FORBID_EDGES[] = 0; GraphPath.FORBID_ROUNDS[] = 0
machine, t = run_once(PATH)
hdr = split(first(l for l in eachline(PATH) if startswith(l, "p cnf")))
open(OUT, "a") do io
    println(io, join((basename(PATH), MODE, hdr[3], hdr[4], SatMachine.have_solution(machine), round(t, digits = 2),
                      GraphPath.FORBID_TRIOS[], GraphPath.FORBID_EDGES[], GraphPath.FORBID_ROUNDS[]), "\t"))
end
