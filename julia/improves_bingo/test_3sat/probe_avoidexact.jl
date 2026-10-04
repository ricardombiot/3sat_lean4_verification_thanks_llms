# AvoidExact, medido directamente (28-sept-2026; lean/improves_bingo KernelSkip.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_avoidexact.jl <salida.tsv> [muestras] [semilla]
#
# AvoidExact f d: toda pareja de una estructura cerrada de f con cimas de hijo permitido está en una camarilla de f
# (que concuerda con P) con cima de hijo permitido. Por el núcleo (Kernel.lean), las estructuras cerradas con cimas
# de hijo permitido son las del estado con las cimas malas matadas, así que AvoidExact equivale a EdgeClique en
#   pin(revisar(f sin las cimas cuya ventana está prohibida), P)
# (las camarillas de ese estado son las de f con cima de hijo permitido que concuerdan con P).
#
# Se redefine GraphPath.do_up_filtering! (mismo código): tras filter!(requires), si alguna cima de f tiene la ventana
# prohibida (la fila la va a saltar), se mide para P vacío y `muestras` conjuntos P de 1 a 3 nodos del mapa.
# Por instancia: skips (UPs con ventana saltada), bad_tops (cimas malas), cmp (estados juzgados), fail (con algo
# sin cubrir), dead (el estado restringido o fijado muere), trunc (demasiadas camarillas).

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
    skips :: Int; bad_tops :: Int; cmp :: Int; fail :: Int; dead :: Int; trunc :: Int
end
const ACC = Ref(Acc(0, 0, 0, 0, 0, 0))

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in og.alive[k]), by = n -> n.index)

function measure!(f, d, prohibited)
    last = f.current_step - 1
    last < 0 && return
    bad = [t for t in PathCollectionLines.get_ids_step(f.table_lines, last)
           if Alias.shift_path_id(t, d) in prohibited]
    isempty(bad) && return
    acc = ACC[]
    acc.skips += 1; acc.bad_tops += length(bad)
    g = deepcopy(f)
    for t in bad
        GraphPath.remove_node_owner!(g, t; rule = :avoid)
    end
    g.review_owners = true
    GraphPath.make_review_owners!(g)
    if !g.is_valid
        acc.dead += 1
        return
    end
    steps = choice_steps(g.og)
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(3, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(g.og, k)) for k in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps
        h = deepcopy(g)
        GraphPath.filter!(h, SetNodesId(P))
        if !h.is_valid
            acc.dead += 1
            continue
        end
        r = GraphPath.edge_clique_miss(h)
        if r === nothing
            acc.trunc += 1
        else
            acc.cmp += 1
            r == (0, 0) || (acc.fail += 1)
        end
    end
end

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        filter!(gpath, requires)
        gpath.is_valid && $(measure!)(gpath, map_id_node, prohibited)
        do_up!(gpath, map_id_node, title, prohibited)
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
        println(io, "instance\tskips\tbad_tops\tcmp\tfail\tdead\ttrunc")
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
            println(io, "$name\t$(a.skips)\t$(a.bad_tops)\t$(a.cmp)\t$(a.fail)\t$(a.dead)\t$(a.trunc)")
            flush(io)
        end
    end
end

main()
