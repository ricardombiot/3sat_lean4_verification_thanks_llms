# Qué regla corta las aristas de un solo lado en la unión fijada (28-sept-2026; lean/improves_bingo UnionSplit.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_side_cut.jl <salida.tsv> [muestras] [semilla]
#
# En cada join válido (e = el que ya estaba, g = el que llega, U = la unión, c = current_step) y cada nodo del mapa
# b del paso c-2 de un lado S (el otro, O), para P vacío y `muestras` P al azar se fija U en P ++ [b] y se vigilan
# las aristas de U entre dos nodos vivos en S que S no tiene (vienen solo de O). Por cada arista vigilada se anota
# la regla que la quita (pair, parents, sons, clean = muere un extremo, require = el pin mata un extremo) y la
# distancia d = (c-2) - (paso más alto de sus extremos); `left` cuenta las que sobreviven (SidePinned: 0).

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 1
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(SEED))
const WATCH = Dict{Tuple{PathNodeId, PathNodeId}, Int}()   # arista vigilada → d
const TALLY = Dict{Tuple{Symbol, Int}, Int}()               # (regla, d) → cuántas
const TOT = Dict{Symbol, Int}()                             # por instancia: joins, watched, left

function hook(k, rule)
    d = pop!(WATCH, k, nothing)
    d === nothing && return
    key = (rule, min(d, 3))
    TALLY[key] = get(TALLY, key, 0) + 1
end

Core.eval(PG, quote
    function remove_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId; rule :: Symbol)
        x == w && return false
        k = edge_key(x, w)
        haskey(g.edges, k) || return false
        delete!(g.edges, k)
        _drop!(g.inc[x], w)
        _drop!(g.inc[w], x)
        REMOVED_BY[rule] = get(REMOVED_BY, rule, 0) + 1
        $(hook)(k, rule)
        return true
    end
end)

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

function measure!(e, g)
    bump!(:joins)
    c = e.current_step
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
    for P in Ps, side in (e, g), b in map_nodes(side.og, c - 2)
        empty!(WATCH)
        for (k, _) in u.og.edges
            x, w = k
            PG.is_alive(side.og, x) && PG.is_alive(side.og, w) && !PG.has_edge(side.og, x, w) || continue
            WATCH[k] = (c - 2) - max(x.id.step, w.id.step)
        end
        isempty(WATCH) && continue
        bump!(:watched, length(WATCH))
        h = deepcopy(u)
        h.review_owners = true
        GraphPath.filter!(h, SetNodesId(vcat(P, [b])))
        if h.is_valid
            bump!(:left, count(k -> haskey(h.og.edges, k), keys(WATCH)))
        else
            bump!(:deadpin, length(WATCH))   # el pin mata la unión: lo que quede vigilado cae con ella
        end
        empty!(WATCH)
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
        println(io, "instance\tjoins\twatched\tleft\tdeadpin\tcuts(regla,d)")
        for path in corpus()
            name = basename(path)
            empty!(TALLY); empty!(TOT)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch err
                println(io, "$name\tERROR $(typeof(err))"); flush(io); continue
            end
            cuts = join(["$(r):$(d)=$(n)" for ((r, d), n) in sort(collect(TALLY))], " ")
            println(io, "$name\t$(get(TOT, :joins, 0))\t$(get(TOT, :watched, 0))\t$(get(TOT, :left, 0))\t$(get(TOT, :deadpin, 0))\t$cuts")
            flush(io)
        end
    end
end

main()
