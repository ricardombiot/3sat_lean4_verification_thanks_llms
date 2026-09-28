# StarGap: el hueco en la estrella de una cima, como propiedad de un solo estado (28-sept-2026; informe v203 §6,
# paso 3; lean/improves_bingo StarLocal.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_stargap.jl <salida.tsv> [muestras] [semilla]
#
# Estrella de una cima t en un estado S: N[t] = t y los nodos que t posee. Para dos nodos x, z de N[t] que S no hace
# poseerse (x ≠ z, ninguno la cima), un paso l (distinto de los suyos) es un hueco si t no posee a ningún vecino común
# de x y z en l. StarGap S: toda pareja así tiene un hueco. Se mide en cada lado de cada join (e y g, antes de juntar),
# fijados en P vacío y `muestras` P al azar:
#   pairs / gap_bad — todas las parejas de la estrella que no se poseen / las que no tienen hueco (StarGap: 0)
#   one / one_bad   — solo las que el otro lado sí hace poseerse (las aristas de un solo lado) / sin hueco

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

function gaps!(S, O, P)
    h = pinned(S, P)
    h.is_valid || return
    c = h.current_step
    for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
        N = collect(PG.neighbors_all(h.og, t))
        Ns = Set(N); push!(Ns, t)
        for i in eachindex(N), j in i+1:length(N)
            x, z = N[i], N[j]
            (x == t || z == t) && continue
            PG.has_edge(h.og, x, z) && continue
            x.id.step == z.id.step && continue
            one = PG.is_alive(O.og, x) && PG.is_alive(O.og, z) && PG.has_edge(O.og, x, z)
            bump!(:pairs); one && bump!(:one)
            hasgap = false
            for l in 0:c-1
                (l == x.id.step || l == z.id.step) && continue
                if !any(w -> w in Ns && PG.has_edge(h.og, z, w), PG.neighbors(h.og, x, l))
                    hasgap = true; break
                end
            end
            if !hasgap
                bump!(:gap_bad); one && bump!(:one_bad)
            end
        end
    end
end

function measure!(e, g)
    for P in samplesP(e)
        gaps!(e, g, P); gaps!(g, e, P)
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

const COLS = (:pairs, :gap_bad, :one, :one_bad)

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
