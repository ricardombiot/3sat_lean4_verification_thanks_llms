# ¿Es (C) un paso inductivo? La hipótesis que necesitaría (28-sept-2026; lean/improves_bingo TopsFrom.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_crosstop.jl <salida.tsv> [muestras] [semilla]
#
# (C) en el paso T+1: una cima viva en la unión fijada tiene su padre vivo en el estado de partida de su llegada,
# fijado igual. Al bajar por el UP, la estructura cae en la unión de los estados de partida de TODAS las llegadas al
# mismo nodo del mapa d: los remitentes s (nodos del mapa distintos) filtrados con los requisitos de d, f_s. Así, (C)
# se sigue de `TopUnion` para esa familia (nodos del mapa distintos, filtro común). Se mide al empezar cada paso:
#   cross_tops / cross_bad — cimas de ∪ f_s fijada en P que no están vivas en su f_s fijado en P (filtro común)
# Y para el paso siguiente haría falta lo mismo con filtros distintos (la familia de todos los f_{s,d}, un mismo
# remitente filtrado para varios hijos):
#   mix_tops / mix_bad_any — la cima no está viva en ningún f_{s,d} fijado que la tenga
#   mix_bad_all — hay algún f_{s,d} que la tiene viva sin fijar y la pierde fijado (hace falta elegir el filtro)

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

function measure_line!(machine)
    gm = GMAP[]
    line = Any[]
    CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, g -> push!(line, g))
    isempty(line) && return
    # f[(s, d)] = s filtrado con los requisitos de d
    F = Dict{Tuple{Int, NodeId}, Any}()
    for (i, s) in enumerate(line)
        for d in SatMachine.map_get_node(gm, s.map_parent_id).sons
            f = pinned(s, collect(SatMachine.map_get_node(gm, d).requires))
            f.is_valid && (F[(i, d)] = f)
        end
    end
    isempty(F) && return
    # filtro común: por destino
    for d in unique(k[2] for k in keys(F))
        members = [(k, f) for (k, f) in F if k[2] == d]
        length(members) >= 2 || continue
        u = union_of([f for (_, f) in members])
        for P in samplesP(u)
            h = pinned(u, P)
            h.is_valid || continue
            for q in tops(h)
                bump!(:cross_tops)
                own = [f for (_, f) in members if PG.is_alive(f.og, q)]
                any(f -> (fp = pinned(f, P); fp.is_valid && PG.is_alive(fp.og, q)), own) || bump!(:cross_bad)
            end
        end
    end
    # filtros distintos: toda la familia
    allf = collect(values(F))
    length(allf) >= 2 || return
    u = union_of(allf)
    for P in samplesP(u)
        h = pinned(u, P)
        h.is_valid || continue
        for q in tops(h)
            bump!(:mix_tops)
            own = [f for f in allf if PG.is_alive(f.og, q)]
            oks = [(fp = pinned(f, P); fp.is_valid && PG.is_alive(fp.og, q)) for f in own]
            any(oks) || bump!(:mix_bad_any)
            all(oks) || bump!(:mix_bad_all)
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

const COLS = (:cross_tops, :cross_bad, :mix_tops, :mix_bad_any, :mix_bad_all)

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
            catch err
                println(io, "$name\tERROR $(typeof(err))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(get(TOT, c, 0)) for c in COLS], "\t"))
            flush(io)
        end
    end
end

main()
