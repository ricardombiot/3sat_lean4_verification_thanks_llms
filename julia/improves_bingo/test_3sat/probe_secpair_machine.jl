# ¿Es SecPair un invariante de la ejecución de la máquina? (28-sept-2026; SecPair.lean, SecInduction.lean)
#
#   julia --project=. test_3sat/probe_secpair_machine.jl <salida.tsv>
#
# La máquina paso a paso (como measure_bingo.jl): tras cada paso, cada gpath de la línea (ya revisado por el UP, el
# join y el filtro de ese paso) se comprueba con GraphPath.sec_pair_bad (by = :map y :node) y GraphPath.pair_closed.
# Por instancia: gpaths mirados, sp_fail / spx_fail (gpaths donde falla SecPair / SecPairX), bad (aristas fuera de
# toda sección, suma), first_fail (primer paso con un fallo, o -), pc_fail (gpaths no cerrados por parejas),
# choice (gpaths con algún paso con elección: los únicos en los que SecPair dice algo).

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

line(machine) = (gs = GPath[]; CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step,
                                                                  g -> push!(gs, g)); gs)

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

function main()
    open(OUT, "w") do io
        println(io, "instance\tsteps\tgpaths\tchoice\tsp_fail\tspx_fail\tbad\tpc_fail\tfirst_fail")
        for path in corpus()
            name = basename(path)
            n = 0; nch = 0; sp = 0; spx = 0; bad = 0; pc = 0; first_fail = "-"; steps = 0
            try
                machine = SatMachine.new(GraphMap.load_import!(path))
                redirect_stdout(devnull) do
                    SatMachine.init!(machine)
                end
                while true
                    steps += 1
                    for g in line(machine)
                        g.is_valid || continue
                        n += 1
                        any(k -> GraphPath.choice_at(g.og, k), 0:g.og.nsteps-1) && (nch += 1)
                        b = GraphPath.sec_pair_bad(g.og; by = :map)
                        bx = GraphPath.sec_pair_bad(g.og; by = :node)
                        GraphPath.pair_closed(g) || (pc += 1)
                        if !isempty(b) || !isempty(bx)
                            first_fail == "-" && (first_fail = string(machine.current_step))
                        end
                        isempty(b) || (sp += 1)
                        isempty(bx) || (spx += 1)
                        bad += length(b)
                    end
                    (!SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)) || break
                    redirect_stdout(devnull) do
                        SatMachine.make_step!(machine)
                    end
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t$steps\t$n\t$nch\t$sp\t$spx\t$bad\t$pc\t$first_fail")
            flush(io)
        end
    end
end

main()
