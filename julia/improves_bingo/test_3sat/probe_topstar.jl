# TopStar: el núcleo de la estrella de una cima la contiene (28-sept-2026; lean/improves_bingo TopExact.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_topstar.jl <salida.tsv> [muestras] [semilla]
#
# Para cada cima t viva en el estado fijado h: se matan todos los vivos fuera de N[t] (t y sus vecinos) y se revisa.
#   star_bad — t no sobrevive (TopStar: 0). Si vale, la estructura que queda vive en N[t], concuerda con el origen
#   de t (sus vecinos en el paso de origen son sus padres) y da TopSplit.
# (Resto: la cabecera de probe_topsplit.jl, de la que sale.)
#
# Estados mirados: la unión de cada join (`u_*`) y cada estado tras un UP (`up_*`), fijados en P vacío y `muestras`
# P al azar (review). Para cada cima t (paso c-1) viva en el estado fijado h, con a = t.parent_id (su origen):
#   split_bad (solo u) — t no sobrevive en h fijado además en a (TopSplit: 0)
#   union_bad (solo u) — t no está viva ni en e ni en g fijados en P (TopUnion: 0)
# La estrella N[t] = t y sus vecinos en h, con las aristas de h entre ellos. StarClosed: N[t] es cerrada:
#   pair_bad — aristas (x,z) de N[t] sin, en algún paso, un vecino común que esté en N[t]
#   node_bad — nodos de N[t] sin padre (paso ≥ 1) o sin hijo (paso < c-1) enlazado y en N[t]
#   link_bad — aristas (x,z), x ≠ z, sin el padre (o el hijo) de la regla de apoyo dentro de N[t]
#   stars — cimas miradas; star_bad — cimas con alguna de las tres

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

docof(h, x) = PathCollectionLines.get_node(h.table_lines, x)

function star!(h, tag)
    c = h.current_step
    for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
        bump!(Symbol(tag, "_stars"))
        N = Set(PG.neighbors_all(h.og, t)); push!(N, t)
        h2 = deepcopy(h)
        for x in collect(GraphPath.alive_ids(h2))
            x in N || GraphPath.remove_node_owner!(h2, x; rule = :star)
        end
        h2.is_valid = h2.og.valid
        h2.review_owners = true
        GraphPath.make_review_owners!(h2)
        (h2.is_valid && PG.is_alive(h2.og, t)) || bump!(Symbol(tag, "_star_bad"))
    end
end

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

function measure_join!(e, g)
    c = e.current_step
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    for P in samplesP(u)
        h = pinned(u, P)
        h.is_valid || continue
        star!(h, "u")
    end
end

function measure_up!(s)
    for P in samplesP(s)
        h = pinned(s, P)
        h.is_valid || continue
        star!(h, "up")
    end
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            $(measure_join!)(gpath, gpath_inmutable)
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
        end
    end
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        gpath.is_valid && $(measure_up!)(gpath)
    end
end)

const COLS = (:u_stars, :u_star_bad, :up_stars, :up_star_bad)

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
