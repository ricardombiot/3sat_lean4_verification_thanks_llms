# KernelUnion: ¿el núcleo de una unión es la unión de los núcleos? (28-sept-2026; Lean Kernel.lean, join)
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_kernelunion.jl <salida.tsv> [muestras] [semilla]
#
# Se redefine GraphPath.do_join! (mismo código): en cada join válido de la máquina, antes de unir, para P vacío y
# `muestras` conjuntos P de 1 a 3 nodos del mapa en pasos con elección distintos (de la unión, al azar):
#   J = aristas de pin(unión, P), A = aristas de pin(g₁, P), B = aristas de pin(g₂, P)  (vacías si el pin muere)
#   miss  = |J ∖ (A ∪ B)|  — aristas del núcleo de la unión que no están en el de ningún lado (KernelUnion: 0)
#   extra = |(A ∪ B) ∖ J|  — lo contrario (se espera 0: la estructura de cada lado sobrevive en la unión)
# Por instancia: joins, cmp (comparaciones), miss_cases, miss, extra_cases, extra.

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 3
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const RNG = Ref(MersenneTwister(SEED))
mutable struct Acc
    joins :: Int; cmp :: Int; miss_cases :: Int; miss :: Int; extra_cases :: Int; extra :: Int
end
const ACC = Ref(Acc(0, 0, 0, 0, 0, 0))

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in og.alive[k]), by = n -> n.index)

function pinned_edges(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true            # P vacío: el review de la unión (el join no revisa)
    GraphPath.filter!(g2, SetNodesId(P))
    return g2.is_valid ? Set(keys(g2.og.edges)) : Set{Tuple{PathNodeId, PathNodeId}}()
end

function measure!(g1, g2)
    acc = ACC[]
    acc.joins += 1
    u = deepcopy(g1)
    PathCollectionLines.union!(u.table_lines, deepcopy(g2).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g2).og)
    steps = choice_steps(u.og)
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(3, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(u.og, k)) for k in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps
        J = pinned_edges(u, P)
        AB = union(pinned_edges(g1, P), pinned_edges(g2, P))
        acc.cmp += 1
        m = length(setdiff(J, AB)); x = length(setdiff(AB, J))
        m > 0 && (acc.miss_cases += 1; acc.miss += m)
        x > 0 && (acc.extra_cases += 1; acc.extra += x)
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
        println(io, "instance\tjoins\tcmp\tmiss_cases\tmiss\textra_cases\textra")
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
            println(io, "$name\t$(a.joins)\t$(a.cmp)\t$(a.miss_cases)\t$(a.miss)\t$(a.extra_cases)\t$(a.extra)")
            flush(io)
        end
    end
end

main()
