# F5 del plan docs/plans/graph_owners.md: medida de tiempo y memoria, improves_bin ↔ improves_bingo.
# Cada máquina en su proceso:
#
#   julia --project=<raíz> measure_bingo.jl <raíz de la máquina> <salida.tsv> [plain|copy]
#
# `copy` solo tiene sentido con improves_bin: le da a sus tablas (PathDocOwners) una copia por
# estructura, como copy_graph en bingo, inyectada desde aquí sin tocar sus fuentes. Así se separa lo que
# gana el grafo de lo que gana no usar el deepcopy genérico.
#
# Por instancia (tras calentar con la primera):
#   time, alloc_mb, gc_s     — @timed de SatMachine.run! (tiempo, memoria reservada en total, GC)
#   peak_mb, peak_own_mb     — el máximo, sobre los pasos, del tamaño vivo de la línea de gpaths
#                              (Base.summarysize) y de su parte de owners (bin: global + tablas de
#                              los nodos; bingo: el grafo)
#   peak_edges_mb            — bingo: la parte del diccionario de aristas dentro del grafo
#   rounds                   — vueltas del review
#   removed                  — bingo: aristas quitadas por regla (PathOwnersGraph.REMOVED_BY)

const ROOT = abspath(ARGS[1])
const OUT = abspath(ARGS[2])
const VARIANT = length(ARGS) >= 3 ? ARGS[3] : "plain"
include(joinpath(ROOT, "src/main.jl"))

# improves_bin no tiene puntos de sonda: allí las vueltas salen de su contador global.
const PROBES = isdefined(AbsSat, :Probes)
PROBES && @eval using .AbsSat.Probes

const GRAPH = isdefined(GraphPath, :owners_table)

if VARIANT == "copy"
    GRAPH && error("la variante copy es para improves_bin")
    @eval Base.deepcopy_internal(o :: PathDocumentOwners.PathDocOwners, d :: IdDict) =
        get!(() -> PathDocumentOwners.PathDocOwners(Dict(k => copy(v) for (k, v) in o.table),
                                                    o.max_step, copy(o.empty_steps), o.valid), d, o)
end

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && push!(files, joinpath(d, f))
        end
    end
    return files
end

mb(x) = round(x / 2^20, digits = 3)

function owners_size(gpath)
    GRAPH && return Base.summarysize(gpath.og)
    s = Base.summarysize(gpath.owners)
    PathCollectionLines.for_each(gpath.table_lines, n -> (s += Base.summarysize(n.owners)))
    return s
end

edges_size(gpath) = GRAPH ? Base.summarysize(gpath.og.edges) : 0

line(machine) = (gs = GPath[]; CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step,
                                                                  g -> push!(gs, g)); gs)

# La máquina paso a paso (como run!), midiendo la línea viva tras cada paso.
function peaks(path)
    machine = SatMachine.new(GraphMap.load_import!(path))
    SatMachine.init!(machine)
    peak = 0; peak_own = 0; peak_edges = 0
    while true
        gs = line(machine)
        peak = max(peak, sum(Base.summarysize, gs; init = 0))
        peak_own = max(peak_own, sum(owners_size, gs; init = 0))
        peak_edges = max(peak_edges, sum(edges_size, gs; init = 0))
        (!SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)) || break
        SatMachine.make_step!(machine)
    end
    return peak, peak_own, peak_edges
end

function timed_run(path)
    machine = SatMachine.new(GraphMap.load_import!(path))
    run() = redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    if PROBES
        Probes.reset!()
        st = @timed Probes.with(run, :review_round => _ -> Probes.bump!(:rounds))
        rounds = Probes.counted(:rounds)
    else
        GraphPath.REVIEW_ROUNDS[] = 0
        st = @timed run()
        rounds = GraphPath.REVIEW_ROUNDS[]
    end
    return st, rounds, SatMachine.have_solution(machine)
end

function main()
    files = corpus()
    timed_run(joinpath(ROOT, "test_window/instances/v5_c20_i1.cnf"))      # calentar
    open(OUT, "w") do io
        println(io, "instance\tsat\ttime\talloc_mb\tgc_s\tpeak_mb\tpeak_own_mb\tpeak_edges_mb\trounds\tremoved")
        for path in files
            name = basename(path)
            local st, rounds, sat, pk
            removed0 = GRAPH ? copy(PathOwnersGraph.REMOVED_BY) : Dict{Symbol, Int}()
            try
                st, rounds, sat = timed_run(path)
                pk = peaks(path)
            catch e
                println(io, "$name\tERROR")
                continue
            end
            removed = ""
            if GRAPH
                # timed_run y peaks corren la máquina dos veces: se cuenta la mitad
                d = Dict(k => (v - get(removed0, k, 0)) ÷ 2 for (k, v) in PathOwnersGraph.REMOVED_BY)
                removed = join(["$k=$(d[k])" for k in sort(collect(keys(d))) if d[k] > 0], ",")
            end
            println(io, "$name\t$sat\t$(round(st.time, digits = 3))\t$(mb(st.bytes))\t" *
                        "$(round(st.gctime, digits = 3))\t$(mb(pk[1]))\t$(mb(pk[2]))\t$(mb(pk[3]))\t$rounds\t$removed")
            flush(io)
        end
    end
end

main()
