# WitAll en todos los pasos, en los estados revisados (28-sept-2026; lean/improves_bingo SplitWitness.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_witall.jl <salida.tsv> [muestras] [semilla]
#
# WitAll g j: si r (paso j) empareja en el núcleo de g fijado en P con y y con w, y (y,w) está en ese núcleo, la
# pareja sobrevive fijando además r.id. Se mide en cada estado tras un UP válido (revisado: `up_*`) y en cada unión
# tras un join (sin revisar: `join_*`), para P vacío y `muestras` P al azar, en cada paso de elección j.
#   cases — ternas (y, w, id del testigo) miradas; bad — las que no sobreviven

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
const TOT = Dict{Symbol, Int}()
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)

function pinned(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(P))
    return g2
end
pinned_edges(h) = h.is_valid ? Set(keys(h.og.edges)) : Set{Tuple{PathNodeId, PathNodeId}}()

wit_ids(h, y, w, k) = Set(r.id for r in PG.neighbors(h.og, y, k) if PG.has_edge(h.og, w, r))
wit_nodes(h, y, w, k, b) = [r for r in PG.neighbors(h.og, y, k) if r.id == b && PG.has_edge(h.og, w, r)]
inE(h, a, b) = h.is_valid && (a == b ? PG.is_alive(h.og, a) : PG.has_edge(h.og, a, b))

function witall!(g0, tag)
    bump!(Symbol(tag, "_states"))
    steps = choice_steps(g0.og)
    isempty(steps) && return
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    for _ in 1:SAMPLES
        m = rand(RNG[], 1:min(2, length(steps)))
        push!(Ps, [rand(RNG[], map_nodes(g0.og, s)) for s in shuffle(RNG[], steps)[1:m]])
    end
    for P in Ps
        h = pinned(g0, P)
        h.is_valid || continue
        for j in steps
            bs = map_nodes(h.og, j)
            length(bs) >= 2 || continue
            hb = Dict(b => pinned(h, [b]) for b in bs)
            for ed in keys(h.og.edges)
                y, w = ed
                (y.id.step == j || w.id.step == j) && continue
                for b in wit_ids(h, y, w, j)
                    bump!(Symbol(tag, "_cases"))
                    inE(hb[b], y, w) || bump!(Symbol(tag, "_bad"))
                end
            end
        end
    end
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
            $(witall!)(gpath, "join")
        end
    end
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        gpath.is_valid && $(witall!)(gpath, "up")
    end
end)

const COLS = (:up_states, :up_cases, :up_bad, :join_states, :join_cases, :join_bad)

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
        println(io, "instance\t" * join(string.(COLS), "\t"))
        for path in corpus()
            name = basename(path)
            empty!(TOT)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(get(TOT, cc, 0)) for cc in COLS], "\t"))
            flush(io)
        end
    end
end

main()
