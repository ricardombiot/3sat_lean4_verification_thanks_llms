# De qué está hecho PinFree: la estructura cerrada máxima (28-sept-2026; LineInduction.lean, PinFreeF).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_pinagree_max.jl <salida.tsv> [muestras] [semilla]
#
# Al empezar cada paso: U = ∪ de la línea; para P vacío y `muestras` P, h = U fijada en P (punto fijo del núcleo).
# Para cada cima t viva en h:
#   M = todos los vivos de h (estructura cerrada máxima que contiene t); C = componente conexa de t en h (por aristas).
#   tops; badM (M no concuerda con rq t.id); badC (C no concuerda); pf_bad (t muere fijada en rq ++ P)
#   nodos de C que discrepan (x en el paso de r ∈ rq con x.id ≠ r):
#     dn, in_star (vecino de t), own (vivo en el estado propio de t), other (solo en estados de otros destinos), both
#     s1, s2, s3p: distancia en pasos desde t (1, 2, ≥3); h2, h3, h4p: saltos desde t en h (2, 3, ≥4)

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


const GMAP = Ref{Any}(nothing)
reqs(gm, d) = collect(SatMachine.map_get_node(gm, d).requires)

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
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(:tops)
            rq = reqs(gm, t.id)
            h2 = pinned(U, vcat(rq, P))
            (h2.is_valid && PG.is_alive(h2.og, t)) || bump!(:pf_bad)
            any(r -> any(x -> x.id.step == r.step && x.id != r, alive), rq) && bump!(:badM)
            dist = Dict(t => 0); q = [t]; i = 1
            while i <= length(q)
                x = q[i]; i += 1
                for z in PG.neighbors_all(h.og, x)
                    (z in alive && !haskey(dist, z)) || continue
                    dist[z] = dist[x] + 1; push!(q, z)
                end
            end
            bad = false
            for r in rq, (x, d) in dist
                (x.id.step == r.step && x.id != r) || continue
                bad = true
                bump!(:dn)
                d <= 1 && bump!(:in_star)
                ino = any(g -> g.map_parent_id == t.id && PG.is_alive(g.og, x), line)
                inx = any(g -> g.map_parent_id != t.id && PG.is_alive(g.og, x), line)
                bump!(ino && inx ? :both : ino ? :own : :other)
                s = (c - 1) - r.step
                bump!(s == 1 ? :s1 : s == 2 ? :s2 : :s3p)
                bump!(d <= 2 ? :h2 : d == 3 ? :h3 : :h4p)
            end
            bad && bump!(:badC)
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

const COLS = (:tops, :badM, :badC, :pf_bad, :dn, :in_star, :own, :other, :both, :s1, :s2, :s3p, :h2, :h3, :h4p)

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
