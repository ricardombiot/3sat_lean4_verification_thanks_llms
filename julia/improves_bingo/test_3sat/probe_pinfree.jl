# PinFree y la estrella con lados = remitentes (28-sept-2026; lean/improves_bingo Lineage.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_pinfree.jl <salida.tsv> [muestras] [semilla]
#
# Al empezar cada paso: U = ∪ de toda la línea (estados de nodos del mapa distintos). Para P vacío y `muestras` P:
#   (1) PinFree: cada cima t viva en U fijada en P (fila D = t.id) sigue viva en U fijada en rq D ++ P.
#       pf_tops, pf_bad
#   (2) Con lados = remitentes (cada estado de la línea) y el pin ampliado rq d ++ P (d un hijo al azar de algún
#       estado): para cada cima p viva en U fijada en rq d ++ P, lado e = su estado fijado igual:
#       st_tops, seps_bad (TopsSep), topstar_bad (TopStar), one, bad_A, k_other (StarKinds, orden A)

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
    length(line) >= 2 || return
    U = deepcopy(line[1])
    for g in line[2:end]
        g2 = deepcopy(g)
        PathCollectionLines.union!(U.table_lines, g2.table_lines)
        PathOwnersGraph.union!(U.og, g2.og)
    end
    U.is_valid = U.og.valid
    c = U.current_step
    alld = unique(d for g in line for d in SatMachine.map_get_node(gm, g.map_parent_id).sons)
    for P in samplesP(U)
        h = pinned(U, P)
        h.is_valid || continue
        # (1)
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(:pf_tops)
            h2 = pinned(U, vcat(reqs(gm, t.id), P))
            (h2.is_valid && PG.is_alive(h2.og, t)) || bump!(:pf_bad)
        end
        # (2)
        isempty(alld) && continue
        d = rand(RNG[], alld)
        Pd = vcat(reqs(gm, d), P)
        hd = pinned(U, Pd)
        hd.is_valid || continue
        sides = [pinned(g, Pd) for g in line]
        for p in collect(get(hd.og.alive, c - 1, SetPathNodesId()))
            ks = [k for (k, sd) in enumerate(sides) if sd.is_valid && PG.is_alive(sd.og, p)]
            isempty(ks) && continue
            bump!(:st_tops)
            length(ks) > 1 && bump!(:seps_bad)
            star_measure!(hd, sides[ks[1]], p, c)
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

const COLS = (:pf_tops, :pf_bad, :st_tops, :seps_bad, :topstar_bad, :one, :nogap, :bad_A, :k_other)

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
