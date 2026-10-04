# StarRestrict en estados sueltos (28-sept-2026; lean/improves_bingo Lineage.lean, TopStarK).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_star_restrict.jl <salida.tsv> [muestras] [semilla]
#
# En cada estado tras un UP (`up_*`) y cada unión tras un join (`jn_*`), fijados en P vacío y `muestras` P (la estructura
# cerrada V = el estado fijado entero): para cada cima t y cada pareja x, z de su estrella (vecinos de t, distintos de t)
# con arista x–z, y cada paso l distinto de los suyos: ¿hay un testigo w en l con aristas a x, a z y a t?
#   pairs — parejas de estrella miradas; bad — sin testigo en algún paso (StarRestrict: 0)
#   tops / tops_bad — cimas con alguna pareja mala
#   above / between / below — pasos que fallan, por encima de la pareja / entre sus pasos / por debajo
#   origin — de los que fallan por encima, cuántos en el paso de origen (c-2)

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

function samplesP(g0)
    steps = choice_steps(g0.og)
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    isempty(steps) && return Ps
    for _ in 1:SAMPLES
        m = rand(RNG[], 1:min(2, length(steps)))
        push!(Ps, [rand(RNG[], map_nodes(g0.og, s)) for s in shuffle(RNG[], steps)[1:m]])
    end
    return Ps
end

function restrict!(g0, tag)
    for P in samplesP(g0)
        h = pinned(g0, P)
        h.is_valid || continue
        c = h.current_step
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(Symbol(tag, "_tops"))
            N = collect(PG.neighbors_all(h.og, t))
            Ns = Set(N)
            anybad = false
            for i in eachindex(N), j in i+1:length(N)
                x, z = N[i], N[j]
                (x == t || z == t) && continue
                PG.has_edge(h.og, x, z) || continue
                bump!(Symbol(tag, "_pairs"))
                lo_, hi_ = minmax(x.id.step, z.id.step)
                bad = false
                for l in 0:c-2
                    (l == x.id.step || l == z.id.step) && continue
                    ok = any(w -> w in Ns && PG.has_edge(h.og, z, w), PG.neighbors(h.og, x, l))
                    if !ok
                        bad = true
                        if l > hi_
                            bump!(Symbol(tag, "_above")); l == c - 2 && bump!(Symbol(tag, "_origin"))
                        elseif l > lo_
                            bump!(Symbol(tag, "_between"))
                        else
                            bump!(Symbol(tag, "_below"))
                        end
                    end
                end
                if bad
                    bump!(Symbol(tag, "_bad")); anybad = true
                end
            end
            anybad && bump!(Symbol(tag, "_tops_bad"))
        end
    end
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
            $(restrict!)(gpath, "jn")
        end
    end
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        gpath.is_valid && $(restrict!)(gpath, "up")
    end
end)

const COLS = Tuple(Symbol(t, '_', c) for t in ("up", "jn") for c in ("tops", "tops_bad", "pairs", "bad", "above", "origin", "between", "below"))

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
