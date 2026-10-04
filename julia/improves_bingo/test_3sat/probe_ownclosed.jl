# PinFree: quitar lo ajeno deja cerrado lo propio (28-sept-2026; LineInduction.lean, PinFreeF).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_ownclosed.jl <salida.tsv> [muestras] [semilla]
#
# U = ∪ de la línea; h = U fijada en P; t cima viva en h; M = componente de t en h; e = estado propio de t fijado en P.
# Propio = vivo en e.
#   tops, noown (t no vive en e)
#   (1) OwnClosed: parejas (x,z) arista de h, x,z ∈ M propios: pairs; pbad (algún paso l sin testigo w ∈ M propio
#       con aristas x–w, z–w en e); noedge (la arista x–z no está en e)
#   (2) orden A / StarKinds con W = M, lado e (sobre las parejas que fallan en (1)): one, nogap, bad_A, k_other
#   (3) puentes: nodos discrepantes x (paso de r ∈ rq, x.id ≠ r) y sus puentes y ∈ N(t) ∩ N(x) en h:
#       dx, br (puentes), br_shared (vivo en e y en otro estado), br_own (solo e), br_for (solo ajeno),
#       tx_own (arista t–y en e), yx_own (arista y–x en e)

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

function measure_line!(machine)
    gm = GMAP[]
    line = Any[]
    CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, g -> push!(line, g))
    isempty(line) && return
    U = deepcopy(line[1])
    for g in line[2:end]
        g2 = deepcopy(g)
        PathCollectionLines.union!(U.table_lines, g2.table_lines)
        PathOwnersGraph.union!(U.og, g2.og)
    end
    U.is_valid = U.og.valid
    c = U.current_step
    for P in samplesP(U)
        h = pinned(U, P)
        h.is_valid || continue
        alive = Set(x for (_, xs) in h.og.alive for x in xs)
        sides = Dict(g.map_parent_id => pinned(g, P) for g in line)
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(:tops)
            e = get(sides, t.id, nothing)
            (e !== nothing && e.is_valid && PG.is_alive(e.og, t)) || (bump!(:noown); continue)
            M = Set([t]); q = [t]; i = 1
            dist = Dict(t => 0)
            while i <= length(q)
                x = q[i]; i += 1
                for z in PG.neighbors_all(h.og, x)
                    (z in alive && !(z in M)) || continue
                    push!(M, z); dist[z] = dist[x] + 1; push!(q, z)
                end
            end
            own(x) = PG.is_alive(e.og, x)
            eE(a, b) = a == b ? own(a) : (own(a) && own(b) && PG.has_edge(e.og, a, b))
            eH(a, b) = a == b || PG.has_edge(h.og, a, b)
            byl = Dict{Int, Vector{PathNodeId}}()
            for x in M; push!(get!(byl, x.id.step, PathNodeId[]), x); end
            # (1)
            F = Tuple{PathNodeId, PathNodeId}[]
            for x in M, z in PG.neighbors_all(h.og, x)
                (z in M && own(x) && own(z) && PG.edge_key(x, z) == (x, z)) || continue
                bump!(:pairs)
                PG.has_edge(e.og, x, z) || bump!(:noedge)
                fl = [l for l in 0:c-1 if !any(w -> own(w) && eE(x, w) && eE(z, w), get(byl, l, PathNodeId[]))]
                isempty(fl) || (bump!(:pbad); push!(F, (x, z)))
            end
            # (2) aristas de M que no están en e
            if !isempty(F)
                inF(a, b) = !(eE(a, b))
                for f in F
                    bump!(:one)
                    x, z = f
                    gaps = [l for l in 0:c-1 if l != x.id.step && l != z.id.step &&
                            !any(w -> eE(x, w) && eE(z, w), get(byl, l, PathNodeId[]))]
                    isempty(gaps) && (bump!(:nogap); continue)
                    wits(l) = [w for w in get(byl, l, PathNodeId[]) if eH(x, w) && eH(z, w)]
                    goodA(l) = all(w -> (inF(x, w) && ORDERS[:A](PG.edge_key(x, w), f)) ||
                                        (inF(z, w) && ORDERS[:A](PG.edge_key(z, w), f)), wits(l))
                    any(goodA, gaps) || bump!(:bad_A)
                    zlow = x.id.step < z.id.step ? x : z
                    kind(l) = (l < lo(f) && all(w -> !(eE(x, w) && eE(z, w)), wits(l))) || isempty(wits(l)) ||
                              (lo(f) < l < hi(f) && all(w -> !eE(zlow, w), wits(l)))
                    any(kind, gaps) || bump!(:k_other)
                end
            end
            # (3)
            for r in reqs(gm, t.id), x in get(byl, r.step, PathNodeId[])
                x.id != r || continue
                bump!(:dx)
                for y in PG.neighbors_all(h.og, t)
                    (y in alive && y != t && PG.has_edge(h.og, y, x)) || continue
                    bump!(:br)
                    oth = any(g -> g.map_parent_id != t.id && sides[g.map_parent_id].is_valid &&
                                   PG.is_alive(sides[g.map_parent_id].og, y), line)
                    bump!(own(y) && oth ? :br_shared : own(y) ? :br_own : :br_for)
                    eE(t, y) && bump!(:tx_own)
                    eE(y, x) && bump!(:yx_own)
                end
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

const COLS = (:tops, :noown, :pairs, :pbad, :noedge, :one, :nogap, :bad_A, :k_other, :dx, :br, :br_shared, :br_own, :br_for, :tx_own, :yx_own)

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
