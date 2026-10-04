# De qué está hecho PinFree (28-sept-2026; lean/improves_bingo LineInduction.lean, PinFreeF).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_pinagree.jl <salida.tsv> [muestras] [semilla]
#
# Al empezar cada paso: U = ∪ de la línea. Para P vacío y `muestras` P, h = U fijada en P, y cada cima t viva en h
# (paso c-1): S = estrella de t en h (t y sus vecinos vivos). ¿S concuerda con rq t.id (en cada paso de un requisito
# r, todo nodo de S tiene id r)?
#   tops, agree (concuerda tal cual), pf_bad (t muere fijada en rq ++ P), bad_agree (concuerda pero muere)
#   tw (discrepa en la ventana: distancia 1..2 desde t), tb (solo más abajo, distancia ≥ 3)
#   nodos que discrepan: n1, n2, n3p por distancia; own (vivos en el estado propio de t fijado en P), other (no)
#   tb_other (cimas cuya discrepancia es solo de nodos ajenos)

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
        own = Dict(g.map_parent_id => pinned(g, P) for g in line)
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            bump!(:tops)
            rq = reqs(gm, t.id)
            h2 = pinned(U, vcat(rq, P))
            dead = !(h2.is_valid && PG.is_alive(h2.og, t))
            dead && bump!(:pf_bad)
            S = Set(x for x in PG.neighbors_all(h.og, t) if PG.is_alive(h.og, x)); push!(S, t)
            ho = get(own, t.id, nothing)
            win = false; below = false; anyown = false
            for r in rq, x in S
                (x.id.step == r.step && x.id != r) || continue
                dist = (c - 1) - r.step
                bump!(dist == 1 ? :n1 : dist == 2 ? :n2 : :n3p)
                isown = ho !== nothing && ho.is_valid && PG.is_alive(ho.og, x)
                bump!(isown ? :own : :other)
                anyown |= isown
                dist <= 2 ? (win = true) : (below = true)
            end
            if !win && !below
                bump!(:agree); dead && bump!(:bad_agree)
            elseif win
                bump!(:tw)
            else
                bump!(:tb); anyown || bump!(:tb_other)
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

const COLS = (:tops, :agree, :pf_bad, :bad_agree, :tw, :tb, :tb_other, :n1, :n2, :n3p, :own, :other)

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
