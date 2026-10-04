# GenAbsorb (28-sept-2026; generalización de Absorb para una inducción que respete la historia).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_genabsorb.jl <salida.tsv>
#
# Al empezar cada paso de la máquina (todos los joins hechos), para cada par ordenado (S, O) de estados de la línea
# (nodos del mapa distintos, mismo paso): U = S ∪ O sin los vivos solo de O, revisada. GenAbsorb: devuelve S.
# Columnas como en probe_absorb.jl (sides = pares mirados). AncKernel (el estado es el núcleo de la ascendencia
# pura sobre sus vivos) se midió FALSO antes de esta sonda: las tablas llevan historia.

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const TOT = Dict{Symbol, Int}()
const GMAP = Ref{Any}(nothing)
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

function absorb!(S, O)
    bump!(:sides)
    u = deepcopy(S)
    o = deepcopy(O)
    PathCollectionLines.union!(u.table_lines, o.table_lines)
    PathOwnersGraph.union!(u.og, o.og)
    for x in collect(GraphPath.alive_ids(u))
        PG.is_alive(S.og, x) || GraphPath.remove_node_owner!(u, x; rule = :absorb)
    end
    u.is_valid = u.og.valid
    bump!(:pre, count(k -> !haskey(S.og.edges, k), keys(u.og.edges)))
    u.review_owners = true
    GraphPath.make_review_owners!(u)
    if !u.is_valid
        bump!(:dead); return
    end
    ex = count(k -> !haskey(S.og.edges, k), keys(u.og.edges))
    lo = count(k -> !haskey(u.og.edges, k), keys(S.og.edges))
    ev = count(x -> !PG.is_alive(S.og, x), GraphPath.alive_ids(u))
    bump!(:extra_e, ex); bump!(:extra_v, ev); bump!(:lost, lo)
    (ex > 0 || ev > 0) && bump!(:bad)
end

function measure_line!(machine)
    line = Any[]
    CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, g -> push!(line, g))
    for S in line, O in line
        S === O && continue
        absorb!(S, O)
    end
end

Core.eval(SatMachine, quote
    function make_step!(machine :: MSat)
        $(measure_line!)(machine)
        current_step = machine.current_step
        CollectionTimeline.for_each_gpath(machine.timeline, current_step, function (gpath)
            send_to_destine_by_origin!(machine, gpath)
        end)
        CollectionTimeline.remove_line!(machine.timeline, current_step)
        machine.current_step += 1
    end
end)

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

const COLS = (:sides, :pre, :bad, :extra_e, :extra_v, :lost, :dead)

function main()
    open(OUT, "w") do io
        println(io, "instance\t" * join(string.(COLS), "\t"))
        for path in corpus()
            name = basename(path)
            empty!(TOT)
            try
                machine = SatMachine.new(LOAD(path))
                GMAP[] = machine.gmap
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch err
                println(io, "$name\tERROR $(typeof(err))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(get(TOT, c, 0)) for c in COLS], "\t"))
            flush(io)
        end
    end
end

main()
