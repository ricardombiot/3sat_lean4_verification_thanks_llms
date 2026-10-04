# StarCore: el núcleo cerrado por parejas de la estrella de una cima, en el marco de PinFree (28-sept-2026).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_starcore.jl <salida.tsv> [muestras] [semilla]
#
# U = ∪ de la línea; h = U fijada en Q (P vacío y `muestras` P); t cima viva en h; W = t y sus vecinos en h.
# R = la mayor relación ⊆ aristas de h en W (con diagonal) cerrada por parejas dentro de W (como star_keep de
# src/graph_path/graph_path_star.jl); V = dominio de R.
#   tops; t_lost (R t t cae); ty_lost (cimas con alguna arista t–y fuera de R); ty_cut (aristas t–y fuera)
#   rpairs (parejas de R), dropped (aristas y–z de h que salen de R)
#   node_bad, par_bad, son_bad (enlaces a padre/hijo dentro de R, docs de la unión), agQ (concordancia con Q)
#   tops_bad (alguna falla de SecStruct)

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

function star_core(og, t, c)
    W = Set{PathNodeId}([t]); foreach(y -> push!(W, y), PG.neighbors_all(og, t))
    R = Dict{PathNodeId, Set{PathNodeId}}(x => Set{PathNodeId}([x]) for x in W)
    ne = 0
    for x in W, z in PG.neighbors_all(og, x)
        z in W && (push!(R[x], z); ne += 1)
    end
    byl = Dict{Int, Vector{PathNodeId}}()
    for x in W; push!(get!(byl, Int(x.id.step), PathNodeId[]), x); end
    ok(a, b) = all(l -> any(w -> w in R[a] && w in R[b], get(byl, l, PathNodeId[])), 0:c-1)
    changed = true
    while changed
        changed = false
        for a in collect(keys(R)), b in collect(R[a])
            haskey(R, a) && b in R[a] || continue
            (a == b || hash(a) < hash(b)) || continue
            ok(a, b) && continue
            changed = true
            if a == b
                for z in R[a]; z == a || delete!(R[z], a); end
                delete!(R, a); filter!(x -> x != a, byl[Int(a.id.step)])
            else
                delete!(R[a], b); delete!(R[b], a)
            end
        end
    end
    return W, R, ne ÷ 2
end

function measure_line!(machine)
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
        getn(x) = PathCollectionLines.get_node(h.table_lines, x)
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(:tops)
            W, R, ne = star_core(h.og, t, c)
            haskey(R, t) || (bump!(:t_lost); bump!(:tops_bad); continue)
            nty = count(y -> y != t && !(y in R[t]), W)
            nty > 0 && bump!(:ty_lost); bump!(:ty_cut, nty)
            nr = sum(length(v) - 1 for v in values(R)) ÷ 2
            bump!(:rpairs, nr); bump!(:dropped, ne - nr)
            Rr(x, z) = haskey(R, x) && z in R[x]
            bad = false
            any(b -> any(x -> x.id.step == b.step && x.id != b, keys(R)), P) && (bump!(:agQ); bad = true)
            for x in keys(R)
                n = getn(x)
                if n === nothing
                    bump!(:node_bad); bad = true; continue
                end
                if (x.parent_id !== nothing && !any(p -> Rr(x, p), n.parents)) ||
                   (x.id.step != c - 1 && !any(s -> Rr(x, s), n.sons))
                    bump!(:node_bad); bad = true
                end
                for w in R[x]
                    w == x && continue
                    if x.id.step >= 1 && !any(p -> Rr(x, p) && Rr(p, w), n.parents)
                        bump!(:par_bad); bad = true
                    end
                    if x.id.step + 1 < c && !any(s -> Rr(x, s) && Rr(s, w), n.sons)
                        bump!(:son_bad); bad = true
                    end
                end
            end
            bad && bump!(:tops_bad)
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

const COLS = (:tops, :t_lost, :ty_lost, :ty_cut, :rpairs, :dropped, :node_bad, :par_bad, :son_bad, :agQ, :tops_bad)

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
