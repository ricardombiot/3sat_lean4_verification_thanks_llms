# OwnRestrict: la estructura máxima de la unión restringida al estado propio SIN fijar (28-sept-2026).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_ownrestrict.jl <salida.tsv> [muestras] [semilla]
#
# U = ∪ de la línea; h = U fijada en P; t cima viva en h; M = componente de t en h; g = estado propio de t (sin fijar,
# sin revisar). V' = M ∩ vivos de g; R' x z = x,z ∈ V' ∧ (x = z ∨ arista de g). Variante R'' = R' ∧ arista de h.
# ¿(V', R') es SecStruct de g con P y t ∈ V'?
#   tops, t_out (t ∉ V'), agP (nodo de V' en el paso de b ∈ P con id ≠ b)
#   pairs, pair_bad (algún paso sin testigo en V' con R'), node_bad, par_bad, son_bad, tops_bad (alguna falla)
#   variante R'': pairs2, bad2 (pair/node/par/son), tops_bad2

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

function check(g, V, Rf, c, cnt)
    getn(x) = PathCollectionLines.get_node(g.table_lines, x)
    byl = Dict{Int, Vector{PathNodeId}}()
    for x in V; push!(get!(byl, x.id.step, PathNodeId[]), x); end
    nb = Dict(x => [z for z in PG.neighbors_all(g.og, x) if z in V && z != x && Rf(x, z)] for x in V)
    R(x, z) = x == z ? (x in V) : (x in V && z in V && Rf(x, z) && PG.has_edge(g.og, x, z))
    bad = false
    for x in V
        n = getn(x)
        if n === nothing
            cnt[:node] += 1; bad = true; continue
        end
        if (x.parent_id !== nothing && !any(p -> R(x, p), n.parents)) ||
           (x.id.step != c - 1 && !any(s -> R(x, s), n.sons))
            cnt[:node] += 1; bad = true
        end
        for z in vcat([x], nb[x])
            hash(x) <= hash(z) || continue
            cnt[:pairs] += 1
            if !all(l -> any(r -> R(x, r) && R(z, r), get(byl, l, PathNodeId[])), 0:c-1)
                cnt[:pair] += 1; bad = true
            end
            x == z && continue
            for (u, w) in ((x, z), (z, x))
                nu = getn(u); nu === nothing && continue
                if u.id.step >= 1 && !any(p -> R(u, p) && R(p, w), nu.parents)
                    cnt[:par] += 1; bad = true
                end
                if u.id.step + 1 < c && !any(s -> R(u, s) && R(s, w), nu.sons)
                    cnt[:son] += 1; bad = true
                end
            end
        end
    end
    return bad
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
        alive = Set(x for (_, xs) in h.og.alive for x in xs)
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(:tops)
            gi = findfirst(g -> g.map_parent_id == t.id, line)
            gi === nothing && (bump!(:t_out); continue)
            g = line[gi]
            M = Set([t]); q = [t]; i = 1
            while i <= length(q)
                x = q[i]; i += 1
                for z in PG.neighbors_all(h.og, x)
                    (z in alive && !(z in M)) || continue
                    push!(M, z); push!(q, z)
                end
            end
            V = Set(x for x in M if PG.is_alive(g.og, x))
            t in V || (bump!(:t_out); continue)
            any(b -> any(x -> x.id.step == b.step && x.id != b, V), P) && bump!(:agP)
            cnt = Dict(:node => 0, :pairs => 0, :pair => 0, :par => 0, :son => 0)
            bad = check(g, V, (x, z) -> true, c, cnt)
            bump!(:pairs, cnt[:pairs]); bump!(:pair_bad, cnt[:pair]); bump!(:node_bad, cnt[:node])
            bump!(:par_bad, cnt[:par]); bump!(:son_bad, cnt[:son]); bad && bump!(:tops_bad)
            cnt2 = Dict(:node => 0, :pairs => 0, :pair => 0, :par => 0, :son => 0)
            bad2 = check(g, V, (x, z) -> PG.has_edge(h.og, x, z), c, cnt2)
            bump!(:pairs2, cnt2[:pairs]); bump!(:bad2, cnt2[:pair] + cnt2[:node] + cnt2[:par] + cnt2[:son])
            bad2 && bump!(:tops_bad2)
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

const COLS = (:tops, :t_out, :agP, :pairs, :pair_bad, :node_bad, :par_bad, :son_bad, :tops_bad, :pairs2, :bad2, :tops_bad2)

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
