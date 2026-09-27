# F4 del plan docs/plans/graph_owners.md: volcado del estado final de una máquina, para el diferencial
# improves_bin ↔ improves_bingo. Las dos definen AbsSat, así que cada una corre en su proceso:
#
#   julia --project=<raíz> dump_final.jl <raíz de la máquina> <carpeta de salida>
#
# Para cada instancia del corpus (el de compare_sym.jl) escribe <salida>/<instancia>.txt con el estado
# final en forma canónica (todo ordenado, ids por Alias.as_key):
#   veredicto, verdad del exhaustivo, soluciones del lector (ordenadas), y por cada gpath de la última
#   línea: sus nodos, sus vivos (la global) y, por nodo, tabla de owners (como conjunto), padres e hijos.
# Y una fila por instancia en <salida>/summary.tsv (veredicto, soluciones ok, vueltas, tiempo).
#
# La tabla sale de node.owners en improves_bin y de GraphPath.owners_table en improves_bingo; en los dos
# casos se escribe como el conjunto de ids de todas sus líneas.

const ROOT = abspath(ARGS[1])
const OUT = abspath(ARGS[2])
include(joinpath(ROOT, "src/main.jl"))

const GRAPH = isdefined(GraphPath, :owners_table)

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

function truth(path)
    ex = replace(replace(path, "/instances/" => "/solver_exhaustive/"), ".cnf" => ".txt")
    isfile(ex) && return strip(first(readlines(ex))) == "SAT"
    try
        s = ExhaustiveSolver.new(path); ExhaustiveSolver.run!(s); return !isempty(s.list_solutions)
    catch
        return nothing
    end
end

key(id) = Alias.as_key(id)
keys_sorted(ids) = join(sort([key(id) for id in ids]), ",")

table_ids(gpath, node) = GRAPH ?
    [w for (_, ws) in something(GraphPath.owners_table(gpath, node.id), Dict()) for w in ws] :
    [w for (_, ws) in node.owners.table for w in ws]

global_ids(gpath) = GRAPH ? collect(GraphPath.alive_ids(gpath)) :
    [w for (_, ws) in gpath.owners.table for w in ws]

function dump_gpath(io, gpath)
    nodes = []
    PathCollectionLines.for_each(gpath.table_lines, n -> push!(nodes, n))
    sort!(nodes, by = n -> key(n.id))
    println(io, "gpath ", key(gpath.map_parent_id), " step=", gpath.current_step, " valid=", gpath.is_valid)
    println(io, "  nodes ", keys_sorted(n.id for n in nodes))
    println(io, "  global ", keys_sorted(global_ids(gpath)))
    for n in nodes
        println(io, "  node ", key(n.id))
        println(io, "    owners ", keys_sorted(table_ids(gpath, n)))
        println(io, "    parents ", keys_sorted(n.parents))
        println(io, "    sons ", keys_sorted(n.sons))
    end
end

function main()
    mkpath(OUT)
    open(joinpath(OUT, "summary.tsv"), "w") do sio
        println(sio, "instance\ttruth\tsat\tsols_ok\tnsols\trounds\ttime")
        for path in corpus()
            name = basename(path)
            tr = truth(path)
            GraphPath.REVIEW_ROUNDS[] = 0
            local machine, t
            try
                machine = SatMachine.new(GraphMap.load_import!(path))
                t = @elapsed redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(sio, "$name\t$(something(tr, "?"))\tERROR\t\t\t\t")
                continue
            end
            rounds = GraphPath.REVIEW_ROUNDS[]
            sat = SatMachine.have_solution(machine)
            sols = String[]
            sols_ok = true
            if sat
                reader = PathExpReader.new(first(SatMachine.get_gpath_solutions(machine)))
                PathExpReader.read!(reader)
                sols = sort([join(Int.(s)) for s in reader.list_solutions])
                sols_ok = !isempty(reader.list_solutions) && CheckerCnf.test_all(reader.list_solutions, path)
            end
            open(joinpath(OUT, "$name.txt"), "w") do io
                println(io, "instance ", name)
                println(io, "truth ", something(tr, "?"), " sat ", sat)
                println(io, "solutions ", length(sols))
                foreach(s -> println(io, "  ", s), sols)
                gpaths = sort(SatMachine.get_gpath_list(machine), by = g -> key(g.map_parent_id))
                foreach(g -> dump_gpath(io, g), gpaths)
            end
            println(sio, "$name\t$(something(tr, "?"))\t$sat\t$sols_ok\t$(length(sols))\t$rounds\t$(round(t, digits = 3))")
            flush(sio)
        end
    end
end

main()
