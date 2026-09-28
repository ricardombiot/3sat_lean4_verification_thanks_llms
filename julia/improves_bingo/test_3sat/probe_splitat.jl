# SplitAt, medido directamente (28-sept-2026; lean/improves_bingo UnionSplit.lean, SideAbsorb.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_splitat.jl <salida.tsv> [muestras] [semilla]
#
# En cada join válido (e, g; U la unión; c = current_step; k = c-2 el paso de origen), para P vacío y `muestras`
# conjuntos P al azar: K = aristas de U fijada en P (review). Para cada arista (y,w) de K:
#   split_bad   — ningún nodo del mapa b del paso k la conserva en U fijada en P ++ [b] (SplitAt: 0)
#   wit_bad     — algún testigo común de y, w en el paso k dentro de K (su id b) no la conserva en P ++ [b]
#                 (WitnessSplit: se puede partir por CUALQUIER testigo)
#   wit_none    — ningún testigo común la conserva (con split_bad = 0, el b bueno no es testigo: raro)
#   pairs       — aristas de K miradas

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
    joins :: Int; pairs :: Int; split_bad :: Int; wit_bad :: Int; wit_none :: Int
end
const ACC = Ref(Acc(0, 0, 0, 0, 0))

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)

function pinned(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(P))
    return g2
end
pinned_edges(h) = h.is_valid ? Set(keys(h.og.edges)) : Set{Tuple{PathNodeId, PathNodeId}}()

function measure!(e, g)
    acc = ACC[]
    acc.joins += 1
    c = e.current_step
    k = c - 2
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    bs = map_nodes(u.og, k)
    steps = [s for s in choice_steps(u.og) if s != k]
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(2, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(u.og, s)) for s in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps
        h = pinned(u, P)
        h.is_valid || continue
        K = pinned_edges(h)
        Kb = Dict(b => pinned_edges(pinned(u, vcat(P, [b]))) for b in bs)
        for ed in K
            y, w = ed
            (y.id.step == k || w.id.step == k) && continue      # las que tocan el origen ya están partidas
            acc.pairs += 1
            any(b -> ed in Kb[b], bs) || (acc.split_bad += 1)
            wit = Set(r.id for r in PG.neighbors(h.og, y, k) if PG.has_edge(h.og, w, r))
            oks = [ed in Kb[b] for b in wit]
            any(!, oks) && (acc.wit_bad += 1)
            (isempty(oks) || !any(oks)) && (acc.wit_none += 1)
        end
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
        println(io, "instance\tjoins\tpairs\tsplit_bad\twit_bad\twit_none")
        for path in corpus()
            name = basename(path)
            ACC[] = Acc(0, 0, 0, 0, 0)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            a = ACC[]
            println(io, "$name\t$(a.joins)\t$(a.pairs)\t$(a.split_bad)\t$(a.wit_bad)\t$(a.wit_none)")
            flush(io)
        end
    end
end

main()
