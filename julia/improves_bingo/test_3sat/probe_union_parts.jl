# Descomponer KernelUnion (28-sept-2026; lean/improves_bingo KernelJoin.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_union_parts.jl <salida.tsv> [muestras] [semilla]
#
# En cada join válido de la máquina (e = el que ya estaba, g = el que llega; U = la unión), con c = current_step:
#   sep_bad      — algún nodo del mapa del paso c-2 está vivo en los dos lados (separación por el origen: 0)
#   shared       — nodos vivos en los dos lados
#   agree_bad    — parejas de nodos compartidos que se poseen en un lado y no en el otro (SharedAgree: 0)
#   pinned_cmp / pinned_bad — para P vacío y `muestras` conjuntos P al azar, y cada nodo del mapa b del paso c-2
#                  de un lado: aristas de pin(U, P ++ [b]) frente a las de pin(lado, P ++ [b]) (PinnedSide)

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 2
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(SEED))
mutable struct Acc
    joins :: Int; sep_bad :: Int; shared :: Int; agree_bad :: Int; pinned_cmp :: Int; pinned_bad :: Int
end
const ACC = Ref(Acc(0, 0, 0, 0, 0, 0))

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)

function pinned_edges(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(P))
    return g2.is_valid ? Set(keys(g2.og.edges)) : Set{Tuple{PathNodeId, PathNodeId}}()
end

function measure!(e, g)
    acc = ACC[]
    acc.joins += 1
    c = e.current_step
    # separación en el paso c-2
    me = Set(map_nodes(e.og, c - 2)); mg = Set(map_nodes(g.og, c - 2))
    isempty(intersect(me, mg)) || (acc.sep_bad += 1)
    # SharedAgree
    sh = [x for x in GraphPath.alive_ids(e) if PG.is_alive(g.og, x)]
    acc.shared += length(sh)
    for i in eachindex(sh), j in i+1:length(sh)
        x, z = sh[i], sh[j]
        PG.has_edge(e.og, x, z) == PG.has_edge(g.og, x, z) || (acc.agree_bad += 1)
    end
    # PinnedSide
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    steps = [k for k in choice_steps(u.og) if k != c - 2]
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(2, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(u.og, k)) for k in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps, (side, bs) in ((e, me), (g, mg)), b in bs
        acc.pinned_cmp += 1
        pinned_edges(u, vcat(P, [b])) == pinned_edges(side, vcat(P, [b])) || (acc.pinned_bad += 1)
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

function main()
    open(OUT, "w") do io
        println(io, "instance\tjoins\tsep_bad\tshared\tagree_bad\tpinned_cmp\tpinned_bad")
        for path in corpus()
            name = basename(path)
            ACC[] = Acc(0, 0, 0, 0, 0, 0)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            a = ACC[]
            println(io, "$name\t$(a.joins)\t$(a.sep_bad)\t$(a.shared)\t$(a.agree_bad)\t$(a.pinned_cmp)\t$(a.pinned_bad)")
            flush(io)
        end
    end
end

main()
