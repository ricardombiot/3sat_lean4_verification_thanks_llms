# El paso inductivo de TopStarK (28-sept-2026; informe v203 §7.5; lean/improves_bingo StarLocal.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_star_step.jl <salida.tsv> [muestras] [semilla]
#
# Una cima t de un estado nuevo tiene un padre p, cima del estado de partida f (el remitente ya filtrado, antes del UP).
# «La estrella de q sostiene a q» en un estado fijado h: el review de h restringido a la estrella de q conserva a q;
# K_q = lo que queda. Se mide, para P vacío y `muestras` P:
#   (A) UP: a = UP(f) (con su review). Para cada cima t de a fijado en P con algún padre p vivo en f fijado en P cuya
#       estrella lo sostiene: ¿el review de a fijado restringido a K_p ∪ {t} conserva a t?
#       up_tops, up_nopar (ningún padre vivo con estrella), up_lift_bad (0 = la subida funciona)
#   (C) Bajada, en cada join (e, g; U la unión): para cada cima t de U fijada en P, con f el estado de partida de la
#       llegada que tiene a t: ¿algún padre de t está vivo en f fijado en P?
#       j_tops, j_down_bad (0 = la bajada funciona: no hace falta mirar la unión)
# (B) join (de la llegada a la unión) es monotonía y no se mide.

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

function restrict_review(h, W)
    h2 = deepcopy(h)
    for x in collect(GraphPath.alive_ids(h2))
        x in W || GraphPath.remove_node_owner!(h2, x; rule = :star)
    end
    h2.is_valid = h2.og.valid
    h2.review_owners = true
    GraphPath.make_review_owners!(h2)
    return h2
end

star_kernel(h, q) = restrict_review(h, push!(Set(PG.neighbors_all(h.og, q)), q))
parents_of(h, t) = [q for q in get(h.og.alive, h.current_step - 1, SetPathNodesId())
                    if q.id == t.parent_id && q.parent_id == t.gparent_id]

const PRE = IdDict{Any, Any}()     # llegada (objeto) → estado de partida filtrado

function measure_up!(f, a)
    for P in samplesP(f)
        fP = pinned(f, P); aP = pinned(a, P)
        (fP.is_valid && aP.is_valid) || continue
        for t in collect(get(aP.og.alive, aP.current_step - 1, SetPathNodesId()))
            bump!(:up_tops)
            Ks = []
            for p in parents_of(fP, t)
                K = star_kernel(fP, p)
                (K.is_valid && PG.is_alive(K.og, p)) && push!(Ks, K)
            end
            if isempty(Ks)
                bump!(:up_nopar); continue
            end
            ok = any(Ks) do K
                W = Set(GraphPath.alive_ids(K)); push!(W, t)
                A = restrict_review(aP, W)
                A.is_valid && PG.is_alive(A.og, t)
            end
            ok || bump!(:up_lift_bad)
        end
    end
end

function measure_join!(e, g)
    fe = get(PRE, e, nothing); fg = get(PRE, g, nothing)
    (fe === nothing || fg === nothing) && return
    c = e.current_step
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    for P in samplesP(u)
        uP = pinned(u, P)
        uP.is_valid || continue
        fP = Dict(true => pinned(fe, P), false => pinned(fg, P))
        for t in collect(get(uP.og.alive, c - 1, SetPathNodesId()))
            bump!(:j_tops)
            f = fP[PG.is_alive(e.og, t)]
            (f.is_valid && !isempty(parents_of(f, t))) || bump!(:j_down_bad)
        end
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
        f = deepcopy(gpath)
        do_up!(gpath, map_id_node, title, prohibited)
        if gpath.is_valid && f.is_valid
            $(measure_up!)(f, gpath)
            $(PRE)[gpath] = f
        end
    end
end)

const COLS = (:up_tops, :up_nopar, :up_lift_bad, :j_tops, :j_down_bad)

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
            empty!(TOT); empty!(PRE)
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
