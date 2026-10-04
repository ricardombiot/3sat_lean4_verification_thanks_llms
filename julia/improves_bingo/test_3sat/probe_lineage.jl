# La hipótesis de inducción indexada por el linaje (28-sept-2026; lean/improves_bingo TopsFrom.lean,
# `topUnion_of_prev`).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_lineage.jl <salida.tsv> [muestras] [semilla]
#
# En cada paso (línea L en T+1, ya con sus joins; L0 la línea anterior, en T). Para una cima t (fila D = t.id) su
# remitente s ∈ L0 es el de clave t.parent_id, y sus padres en s son los nodos de la cima de s con ids compatibles.
#   (1) Verdad. U = ∪ L (toda la línea). Para P vacío y `muestras` P: cada cima t viva en U fijada en P tiene algún
#       padre vivo en filtrar(s, req D) fijado en P.            → t1_tops, t1_bad
#   (2) Reproducción con la misma forma, un paso más abajo: G = ∪ de las copias filtrar(u, req D') (u ∈ L, D' hijo
#       de u). Para cada cima t viva en G fijada en P y cada hijo D' de D con t viva en filtrar(u_D, req D') fijado
#       en P (su linaje sigue por D'): algún padre de t vivo en filtrar(s, req D ++ req D') fijado en P.
#                                                              → t2_cases, t2_bad
#   t2_any_bad — cimas de G fijada sin ningún D' que la mantenga (el linaje no sigue por ninguna copia)

using Random
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 1
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
const RNG = Ref(MersenneTwister(SEED))

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const TOT = Dict{Symbol, Int}()
const GMAP = Ref{Any}(nothing)
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)

function pinned(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(P))
    return g2
end

function union_of(fs)
    u = deepcopy(fs[1])
    for f in fs[2:end]
        f2 = deepcopy(f)
        PathCollectionLines.union!(u.table_lines, f2.table_lines)
        PathOwnersGraph.union!(u.og, f2.og)
    end
    u.is_valid = u.og.valid
    return u
end

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

tops(h) = collect(get(h.og.alive, h.current_step - 1, SetPathNodesId()))
parents_in(h, t) = [q for q in get(h.og.alive, h.current_step - 1, SetPathNodesId())
                    if q.id == t.parent_id && q.parent_id == t.gparent_id]
reqs(gm, d) = collect(SatMachine.map_get_node(gm, d).requires)
const PREV = Ref{Any}(nothing)

function measure_line!(machine)
    gm = GMAP[]
    line = Any[]
    CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, g -> push!(line, g))
    prev = PREV[]
    PREV[] = [deepcopy(g) for g in line]
    (prev === nothing || isempty(line)) && return
    bykey = Dict(g.map_parent_id => g for g in prev)
    byD = Dict(g.map_parent_id => g for g in line)
    sender(t) = get(bykey, t.parent_id, nothing)
    # (1)
    U = union_of(line)
    for P in samplesP(U)
        h = pinned(U, P)
        h.is_valid || continue
        for t in tops(h)
            s = sender(t); s === nothing && continue
            bump!(:t1_tops)
            f = pinned(pinned(s, reqs(gm, t.id)), P)
            (f.is_valid && !isempty(parents_in(f, t))) || bump!(:t1_bad)
        end
    end
    # (2)
    copies = Any[]
    for u in line, D2 in SatMachine.map_get_node(gm, u.map_parent_id).sons
        c = pinned(u, reqs(gm, D2)); c.is_valid && push!(copies, c)
    end
    isempty(copies) && return
    G = union_of(copies)
    for P in samplesP(G)
        h = pinned(G, P)
        h.is_valid || continue
        for t in tops(h)
            s = sender(t); s === nothing && continue
            uD = get(byD, t.id, nothing); uD === nothing && continue
            anyD = false
            for D2 in SatMachine.map_get_node(gm, t.id).sons
                c = pinned(pinned(uD, reqs(gm, D2)), P)
                (c.is_valid && PG.is_alive(c.og, t)) || continue
                anyD = true
                bump!(:t2_cases)
                f = pinned(pinned(s, vcat(reqs(gm, t.id), reqs(gm, D2))), P)
                (f.is_valid && !isempty(parents_in(f, t))) || bump!(:t2_bad)
            end
            anyD || bump!(:t2_any_bad)
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

const COLS = (:t1_tops, :t1_bad, :t2_cases, :t2_bad, :t2_any_bad)

function main()
    open(OUT, "w") do io
        println(io, "instance\t" * join(string.(COLS), "\t"))
        for path in corpus()
            name = basename(path)
            empty!(TOT); PREV[] = nothing
            try
                machine = SatMachine.new(LOAD(path))
                GMAP[] = machine.gmap
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch err
                println(io, "$name\tERROR $(typeof(err))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(get(TOT, c, 0)) for c in COLS], "\t"))
            flush(io)
        end
    end
end

main()
