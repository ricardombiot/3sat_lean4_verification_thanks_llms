# ConeClosed, el paso de la inducción descendente de SideEdges por conos (28-sept-2026; SideDescent.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_cone_closed.jl <salida.tsv>
#
# En cada join, para cada lado S y cada pareja de un solo lado (x,z) (arista del otro lado, vivos en S, sin arista
# en S) con m = paso más alto de los dos ≤ c-3: ¿tienen x y z un vecino común en S en cada paso l, m < l ≤ c-1
# (cono completo)? `cone` cuenta las que sí: cada una es un contraejemplo de ConeClosed en S.
#
# (Lo que sigue es la cabecera de probe_son_closed.jl, de la que sale.)
#
# En cada join válido (lados S = e, g; O el otro) y cada arista (x,z) de O que S no tiene con x, z vivos en S
# (de un solo lado), con x el más alto (paso m) y m + 1 < c: ¿hay en S un hijo s de x (compatible, x–s arista)
# con s–z arista de S? Si sí (`sonhit`), el paso inductivo no puede cerrar solo con los hijos: S tiene la
# configuración (x–s, s–z, sin x–z). `pairs` cuenta las aristas miradas.

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const TOT = Dict{Symbol, Int}()
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

compat(p, y) = y.parent_id == p.id && y.gparent_id == p.parent_id && p.id.step + 1 == y.id.step

function side!(S, O, c)
    for (k, _) in O.og.edges
        a, b = k
        PG.is_alive(S.og, a) && PG.is_alive(S.og, b) && !PG.has_edge(S.og, a, b) || continue
        for (x, z) in ((a, b), (b, a))
            x.id.step >= z.id.step || continue
            x.id.step + 1 < c || continue
            bump!(:pairs)
            hit = any(s -> s != z && compat(x, s) && PG.has_edge(S.og, s, z),
                      PG.neighbors(S.og, x, x.id.step + 1))
            hit && bump!(:sonhit)
            x.id.step <= c - 3 || continue
            full = all(l -> any(t -> PG.has_edge(S.og, t, z), PG.neighbors(S.og, x, l)), x.id.step+1:c-1)
            full && bump!(:cone)
        end
    end
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            c = gpath.current_step
            $(side!)(gpath, gpath_inmutable, c)
            $(side!)(gpath_inmutable, gpath, c)
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
        end
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

function main()
    open(OUT, "w") do io
        println(io, "instance\tpairs\tsonhit\tcone")
        for path in corpus()
            name = basename(path)
            empty!(TOT)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch err
                println(io, "$name\tERROR $(typeof(err))"); flush(io); continue
            end
            println(io, "$name\t$(get(TOT, :pairs, 0))\t$(get(TOT, :sonhit, 0))\t$(get(TOT, :cone, 0))")
            flush(io)
        end
    end
end

main()
