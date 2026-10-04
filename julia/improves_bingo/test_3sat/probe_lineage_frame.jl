# El marco de T−1 de la inducción conjunta (28-sept-2026; lean/improves_bingo Lineage.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_lineage_frame.jl <salida.tsv> [muestras] [semilla]
#
# Al empezar cada paso: todas las copias c(s, d) = s filtrado con los requisitos de d, para cada estado s de la línea y
# cada hijo d de s (filtros DISTINTOS; un mismo remitente aparece en varias copias con los mismos ids). M = ∪ copias,
# fijada en P (P vacío y `muestras` P). Para cada cima p viva en M fijada y cada copia de linaje e = c(s_p, d) que la
# tiene viva (fijada en P), con el otro lado = el resto de copias:
#   cases
#   seps_bad    — TopsSep: p viva también en otra copia (fijada en P)
#   seps_same   — ... y esa otra copia es del mismo remitente (otro destino)
#   topstar_bad — TopStar: el review de la estrella de p en M fijada la pierde
#   one, nogap, bad_A, k_other — StarKinds / orden A con e como lado

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

hi(f) = max(f[1].id.step, f[2].id.step)
lo(f) = min(f[1].id.step, f[2].id.step)
const ORDERS = Dict(
    :A => (a, b) -> (hi(a), lo(a)) < (hi(b), lo(b)),
    :B => (a, b) -> (lo(a), hi(a)) < (lo(b), hi(b)),
    :C => (a, b) -> (-hi(a), lo(a)) < (-hi(b), lo(b)),
    :D => (a, b) -> (-hi(a), -lo(a)) < (-hi(b), -lo(b)))

const GMAP = Ref{Any}(nothing)
reqs(gm, d) = collect(SatMachine.map_get_node(gm, d).requires)

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

function star_measure!(h, hS, t, c)
    W = Set(PG.neighbors_all(h.og, t)); push!(W, t)
    A = restrict_review(h, W)
    (A.is_valid && PG.is_alive(A.og, t)) || bump!(:topstar_bad)
    eS(a, b) = PG.is_alive(hS.og, a) && PG.is_alive(hS.og, b) && PG.has_edge(hS.og, a, b)
    F = Set{Tuple{PathNodeId, PathNodeId}}()
    for x in W, z in PG.neighbors_all(h.og, x)
        (z != x && z in W) || continue
        eS(x, z) || push!(F, PG.edge_key(x, z))
    end
    inF(a, b) = PG.edge_key(a, b) in F
    for f in F
        bump!(:one)
        x, z = f
        gaps = [l for l in 0:c-1 if l != x.id.step && l != z.id.step &&
                !any(w -> w in W && eS(x, w) && eS(z, w), get(h.og.alive, l, SetPathNodesId()))]
        isempty(gaps) && (bump!(:nogap); continue)
        wits(l) = [w for w in get(h.og.alive, l, SetPathNodesId()) if w in W && PG.has_edge(h.og, x, w) && PG.has_edge(h.og, z, w)]
        goodA(l) = all(w -> (inF(x, w) && ORDERS[:A](PG.edge_key(x, w), f)) || (inF(z, w) && ORDERS[:A](PG.edge_key(z, w), f)), wits(l))
        any(goodA, gaps) || bump!(:bad_A)
        zlow = x.id.step < z.id.step ? x : z
        kind(l) = (l < lo(f) && all(w -> !(eS(x, w) && eS(z, w)), wits(l))) || isempty(wits(l)) ||
                  (lo(f) < l < hi(f) && all(w -> !eS(zlow, w), wits(l)))
        any(kind, gaps) || bump!(:k_other)
    end
end

function measure_line!(machine)
    gm = GMAP[]
    line = Any[]
    CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, g -> push!(line, g))
    copies = Any[]      # (índice del remitente, copia)
    for (i, s) in enumerate(line), d in SatMachine.map_get_node(gm, s.map_parent_id).sons
        cp = pinned(s, reqs(gm, d))
        cp.is_valid && push!(copies, (i, cp))
    end
    length(copies) >= 2 || return
    M = deepcopy(copies[1][2])
    for (_, cp) in copies[2:end]
        c2 = deepcopy(cp)
        PathCollectionLines.union!(M.table_lines, c2.table_lines)
        PathOwnersGraph.union!(M.og, c2.og)
    end
    M.is_valid = M.og.valid
    c = M.current_step
    for P in samplesP(M)
        h = pinned(M, P)
        h.is_valid || continue
        cps = [(i, pinned(cp, P)) for (i, cp) in copies]
        for p in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            lin = [k for (k, (i, cpP)) in enumerate(cps) if cpP.is_valid && PG.is_alive(cpP.og, p)]
            for k in lin
                bump!(:cases)
                others = [j for j in lin if j != k]
                if !isempty(others)
                    bump!(:seps_bad)
                    any(j -> cps[j][1] == cps[k][1], others) && bump!(:seps_same)
                end
                star_measure!(h, cps[k][2], p, c)
            end
        end
    end
end

Core.eval(SatMachine, quote
    function make_step!(machine :: MSat)
        $(measure_line!)(machine)
        current_step = machine.current_step
        CollectionTimeline.for_each_gpath(machine.timeline, current_step, function (gpath)
            send_to_destine_by_origin!(machine, gpath)
        end)
        CollectionTimeline.remove_line!(machine.timeline, current_step)
        machine.current_step += 1
    end
end)

const COLS = (:cases, :seps_bad, :seps_same, :topstar_bad, :one, :nogap, :bad_A, :k_other)

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
                GMAP[] = machine.gmap
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
