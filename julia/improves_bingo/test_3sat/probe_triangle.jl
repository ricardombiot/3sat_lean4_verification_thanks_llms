# El triángulo de OwnSideGood (28-sept-2026; lean/improves_bingo SplitWitness.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_triangle.jl <salida.tsv> [muestras] [semilla]
#
# En cada join (e, g; U la unión; k = c-2), para P vacío y `muestras` P, y cada origen b (lado S = el que lo tiene
# vivo): las parejas (y,w) de U fijada en P (sin extremos en k) que son aristas de S y tienen un testigo r de id b
# en U fijada en P (casos de OwnSideGood). Para cada caso:
#   own_bad  — (y,w) no sobrevive en U fijada en P ++ [b] (OwnSideGood: 0)
#   tri_out  — alguna de y–w, y–r, w–r no está en S fijado en P (el triángulo no es del núcleo del lado)
#   side_bad — (y,w) no sobrevive en S fijado en P ++ [b] (con el triángulo dentro: el enunciado solo sobre S)
# Y dentro de cada lado S, sin la unión: parejas de S fijado en P con un testigo de id b en S fijado en P:
#   sw_cases / sw_bad — la pareja no sobrevive en S fijado en P ++ [b] (¿cualquier testigo sirve dentro de un lado?)

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

function measure!(e, g)
    bump!(:joins)
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
        hu = pinned(u, P)
        hu.is_valid || continue
        hs = Dict(:e => pinned(e, P), :g => pinned(g, P))
        for b in bs
            sk = any(x -> x.id == b, get(e.og.alive, k, SetPathNodesId())) ? :e : :g
            S = sk == :e ? e : g
            hS = hs[sk]
            hub = pinned(hu, [b])
            hSb = hS.is_valid ? pinned(hS, [b]) : hS
            for ed in keys(hu.og.edges)
                y, w = ed
                (y.id.step == k || w.id.step == k) && continue
                PG.has_edge(S.og, y, w) || continue
                rs = wit_nodes(hu, y, w, k, b)
                isempty(rs) && continue
                bump!(:cases)
                inE(hub, y, w) || bump!(:own_bad)
                all(r -> !(inE(hS, y, w) && inE(hS, y, r) && inE(hS, w, r)), rs) && bump!(:tri_out)
                inE(hSb, y, w) || bump!(:side_bad)
            end
            if hS.is_valid
                for ed in keys(hS.og.edges)
                    y, w = ed
                    (y.id.step == k || w.id.step == k) && continue
                    b in wit_ids(hS, y, w, k) || continue
                    bump!(:sw_cases)
                    inE(hSb, y, w) || bump!(:sw_bad)
                end
            end
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

const COLS = (:joins, :cases, :own_bad, :tri_out, :side_bad, :sw_cases, :sw_bad)

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
