# Comprobación final del review (FINAL_CHECK, propuesta del informe v201): ¿cambia algo, se pierde alguna solución?
# Migrada al microframework de probes (probes_lib.jl, src/utils/probes.jl): las cuentas salen de los puntos de
# sonda :review_round, :final_run y :final_cut.
#
#   julia --project=. test_3sat/probe_final_check.jl <salida.tsv>
#
# Para cada instancia y cada mapa (clásico: load_import!, lector desde el paso 0; bin: load_import_bin!, desde el 1)
# se corre la máquina y el lector (PathExpReader, todas las ramas) con GraphPath.FINAL_CHECK = :off y = :on:
#   truth                    — verdad del exhaustivo (fichero o ExhaustiveSolver)
#   v_off, v_on              — veredictos de la máquina
#   ns_off, ns_on, ns_ex     — número de soluciones del lector y del exhaustivo
#   sols_same                — mismas soluciones del lector con :off y :on
#   sols_ok                  — con :on, las soluciones del lector son exactamente las del exhaustivo (y pasan el
#                              comprobador de cláusulas); «?» si no hay exhaustivo
#   state_same               — misma línea final (vivos, aristas, nodos y enlaces de cada gpath)
#   rounds_off, rounds_on    — vueltas de review (máquina y lector)
#   final_runs, final_cuts   — comprobaciones finales hechas / que cambiaron algo (máquina y lector, con :on)
#   t_off, t_on              — tiempo de máquina + lector

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step
using .AbsSat.Probes

key(id) = Alias.as_key(id)

function fingerprint(machine)
    gs = SatMachine.get_gpath_list(machine)
    out = String[]
    for g in gs
        nodes = String[]
        PathCollectionLines.for_each(g.table_lines, n -> push!(nodes,
            key(n.id) * "|p:" * join(sort(key.(collect(n.parents))), ",") * "|s:" * join(sort(key.(collect(n.sons))), ",")))
        push!(out, string(key(g.map_parent_id), " valid=", g.is_valid,
            " alive=", join(sort(key.(collect(GraphPath.alive_ids(g)))), ","),
            " edges=", join(sort([key(a) * "-" * key(b) for (a, b) in keys(g.og.edges)]), ","),
            " nodes=", join(sort(nodes), ";")))
    end
    return join(sort(out), "\n")
end

function run(path, loader, first_lit, mode)
    GraphPath.FINAL_CHECK[] = mode
    Probes.reset!()
    machine = SatMachine.new(loader(path))
    sols = Set{String}()
    t = @elapsed Probes.with(:review_round => _ -> Probes.bump!(:rounds),
                             :final_run => _ -> Probes.bump!(:runs),
                             :final_cut => _ -> Probes.bump!(:cuts)) do
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
        if SatMachine.have_solution(machine)
            reader = PathExpReader.new(deepcopy(first(SatMachine.get_gpath_solutions(machine))), first_lit)
            redirect_stdout(devnull) do
                PathExpReader.read!(reader)
            end
            sols = Set(join(Int.(s)) for s in reader.list_solutions)
        end
    end
    return (sat = SatMachine.have_solution(machine), sols = sols, fp = fingerprint(machine), t = t,
            rounds = Probes.counted(:rounds), runs = Probes.counted(:runs), cuts = Probes.counted(:cuts))
end

function main()
    header = "instance\tmap\ttruth\tv_off\tv_on\tns_off\tns_on\tns_ex\tsols_same\tsols_ok\tstate_same\t" *
             "rounds_off\trounds_on\tfinal_runs\tfinal_cuts\tt_off\tt_on"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf"]),
                           variants = ProbeLib.MAPS) do path, (_, loader, fl)
        ex = ProbeLib.exhaustive(path)
        a = run(path, loader, fl, :off)
        b = run(path, loader, fl, :on)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        ok = ex === nothing ? "?" :
             string(b.sols == ex && (isempty(b.sols) || CheckerCnf.test_all([BitVector(c == '1' for c in s) for s in b.sols], path)))
        return (truth, a.sat, b.sat, length(a.sols), length(b.sols), ex === nothing ? "?" : length(ex),
                a.sols == b.sols, ok, a.fp == b.fp, a.rounds, b.rounds, b.runs, b.cuts,
                round(a.t, digits = 3), round(b.t, digits = 3))
    end
    GraphPath.FINAL_CHECK[] = :off
end

main()
