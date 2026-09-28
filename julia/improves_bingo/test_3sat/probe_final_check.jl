# Comprobación final del review (FINAL_CHECK, propuesta del informe v201): ¿cambia algo, se pierde alguna solución?
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

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances"),
            joinpath(ROOT, "../../lean/improves_bin/cnf/crafted")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && f != "tseitin_petersen_H.cnf" && push!(files, joinpath(d, f))
        end
    end
    return files
end

function exhaustive(path)
    ex = replace(replace(path, "/instances/" => "/solver_exhaustive/"), ".cnf" => ".txt")
    if isfile(ex)
        ls = strip.(readlines(ex))
        return first(ls) == "SAT" ? Set(String.(ls[2:end])) : Set{String}()
    end
    try
        s = ExhaustiveSolver.new(path); ExhaustiveSolver.run!(s)
        return Set(join(Int.(x)) for x in s.list_solutions)
    catch
        return nothing
    end
end

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
    GraphPath.REVIEW_ROUNDS[] = 0
    GraphPath.FINAL_RUNS[] = 0
    GraphPath.FINAL_CUTS[] = 0
    machine = SatMachine.new(loader(path))
    sols = Set{String}()
    t = @elapsed begin
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
            rounds = GraphPath.REVIEW_ROUNDS[], runs = GraphPath.FINAL_RUNS[], cuts = GraphPath.FINAL_CUTS[])
end

function main()
    open(OUT, "w") do io
        println(io, "instance\tmap\ttruth\tv_off\tv_on\tns_off\tns_on\tns_ex\tsols_same\tsols_ok\tstate_same\t" *
                    "rounds_off\trounds_on\tfinal_runs\tfinal_cuts\tt_off\tt_on")
        for path in corpus(), (mname, loader, fl) in (("classic", GraphMap.load_import!, Step(0)),
                                                       ("bin", GraphMapBin.load_import_bin!, Step(1)))
            name = basename(path)
            ex = exhaustive(path)
            local a, b
            try
                a = run(path, loader, fl, :off)
                b = run(path, loader, fl, :on)
            catch e
                println(io, "$name\t$mname\tERROR $(typeof(e))"); flush(io); continue
            end
            truth = ex === nothing ? "?" : string(!isempty(ex))
            ok = ex === nothing ? "?" :
                 string(b.sols == ex && (isempty(b.sols) || CheckerCnf.test_all([BitVector(c == '1' for c in s) for s in b.sols], path)))
            println(io, "$name\t$mname\t$truth\t$(a.sat)\t$(b.sat)\t$(length(a.sols))\t$(length(b.sols))\t" *
                        "$(ex === nothing ? "?" : length(ex))\t$(a.sols == b.sols)\t$ok\t$(a.fp == b.fp)\t" *
                        "$(a.rounds)\t$(b.rounds)\t$(b.runs)\t$(b.cuts)\t$(round(a.t, digits = 3))\t$(round(b.t, digits = 3))")
            flush(io)
        end
    end
    GraphPath.FINAL_CHECK[] = :off
end

main()
