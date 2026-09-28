# Desdoblar los nodos compartidos en el join: ¿hay una cota? (28-sept-2026; informe v202 §6, idea de Ricardo).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_split_nodes.jl <salida.tsv>
#
# Idea: en el join, un nodo compartido x cuya tabla difiere entre los lados no se funde, queda en «superposición»
# (una copia por lado); se vuelven a fundir cuando las tablas coinciden. La tabla que cuenta es la parte compartida:
# los vecinos de x entre los nodos vivos en los dos lados (la parte de arriba, cimas y orígenes, es siempre de un
# lado y no impide fundir). No se cambia la máquina: se mide.
#
# En cada join válido (e, g) con c = current_step:
#   shared    — nodos vivos en los dos lados
#   sup       — de ellos, los que están en superposición (tabla compartida distinta)
# Y para cada hijo d' del nodo del mapa (el envío siguiente), fijando cada lado en los requisitos de d' (filter!,
# con su review), entre los nodos vivos en los dos lados fijados (los dos válidos):
#   pins      — pares (join, hijo) con los dos lados válidos
#   sup_pin   — nodos que siguen en superposición tras el pin (suma)
#   sup_max   — el máximo de sup_pin en un par
#   persist   — pares con sup_pin > 0 (la superposición pasa al paso siguiente)
#   sup_kill  — nodos de sup que el pin mata en algún lado (colapso por muerte)

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const TOT = Dict{Symbol, Int}()
const GMAP = Ref{Any}(nothing)
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

shared_table(og, x, shared) = Set(w for w in PG.neighbors_all(og, x) if w != x && w in shared)

function superposed(a, b)
    sh = Set(x for x in GraphPath.alive_ids(a) if PG.is_alive(b.og, x))
    sup = [x for x in sh if shared_table(a.og, x, sh) != shared_table(b.og, x, sh)]
    return sh, sup
end

function measure!(e, g)
    bump!(:joins)
    sh, sup = superposed(e, g)
    bump!(:shared, length(sh)); bump!(:sup, length(sup))
    isempty(sup) && return
    d = e.map_parent_id
    gm = GMAP[]
    for son in SatMachine.map_get_node(gm, d).sons
        req = SatMachine.map_get_node(gm, son).requires
        pe = deepcopy(e); pg = deepcopy(g)
        GraphPath.filter!(pe, req); GraphPath.filter!(pg, req)
        pe.is_valid && pg.is_valid || continue
        bump!(:pins)
        killed = count(x -> !(PG.is_alive(pe.og, x) && PG.is_alive(pg.og, x)), sup)
        bump!(:sup_kill, killed)
        _, sup2 = superposed(pe, pg)
        n = length(sup2)
        bump!(:sup_pin, n)
        n > 0 && bump!(:persist)
        TOT[:sup_max] = max(get(TOT, :sup_max, 0), n)
    end
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            $(measure!)(gpath, gpath_inmutable)
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

const COLS = (:joins, :shared, :sup, :pins, :sup_pin, :sup_max, :persist, :sup_kill)

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
