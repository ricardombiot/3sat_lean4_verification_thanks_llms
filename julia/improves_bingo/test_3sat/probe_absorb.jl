# Absorb (28-sept-2026; lean/improves_bingo SideAbsorb.lean; informe v202 §6, argumento global).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_absorb.jl <salida.tsv>
#
# En cada join válido (e, g), para cada lado S (el otro, O): la unión U = S ∪ O sin los nodos vivos solo en O
# (se matan con remove_node_owner!), revisada. Absorb S: el review devuelve S (mismos vivos, mismas aristas).
#   sides    — lados mirados
#   extra_e  — aristas de más que sobreviven (suma), bad — lados con alguna de más (Absorb falla)
#   extra_v  — vivos de más, lost — aristas de S que el review quita (debería ser 0: S está cerrado)
#   dead     — lados cuyo estado revisado muere
#   pre      — aristas de más antes del review (lo que hay que absorber; que no sea 0 comprueba que la medida no es
#              vacía)

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

function measure!(e, g)
    absorb!(e, g)
    absorb!(g, e)
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
