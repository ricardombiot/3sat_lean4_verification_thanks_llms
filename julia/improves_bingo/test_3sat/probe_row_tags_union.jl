# ¿La unión sale por construcción con las etiquetas? (29-sept-2026, rama row-tags, informe v204 §7.7 paso 3)
#
#   PROBE_MAP=bin ROW_TAGS=on test_3sat/run_capped.sh <tope_MB> <tope_s> julia --heap-size-hint=<G> --project=. \
#       test_3sat/probe_row_tags_union.jl <salida.tsv> [muestras] [semilla]
#
# En cada join de la máquina se guardan las llegadas (la primera y cada una que se une). Tras el join, para Q = []
# y `muestras` pins al azar (1–2 nodos del mapa en pasos con elección), se fija y revisa la unión J y cada llegada A
# con el review etiquetado, y se comprueba, en la fila del join ℓ (la última marcada) y para la clave a de cada A:
#   pnode — nodos de J fijada con a en la fila ℓ que no están vivos en A fijada
#   pedge — aristas de J fijada con a en la fila ℓ que no están en A fijada
#   ptop  — cimas de J fijada que no están vivas en la llegada de su clave, fijada igual (TopUnion)
# Si las tres son 0, la pieza de cada clave está dentro de su llegada: la unión sale por la regla.
# Además: joins, pins (fijaciones de J hechas), jdead (J fijada inválida: no hay nada que comprobar), adead (A
# fijada inválida con su pieza en J no vacía: cuenta como fallo de pnode), bits (claves quitadas en todo).
# Con PROBE_ONLY=a.cnf,b.cnf solo esas instancias.

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 2
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929
include(joinpath(ROOT, "src/main.jl"))

PathOwnersGraph.tags_on() || error("esta sonda necesita ROW_TAGS=on")
const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(SEED))
const TOT = Dict{Symbol, Int}()
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

# ---------------- las llegadas de cada join ----------------

const ARR = Dict{Tuple{Int, NodeId}, Vector{GraphPath.GPath}}()

function before_join(gpath, gin)
    GraphPath.is_valid_join(gpath, gin) || return
    key = (Int(gpath.current_step), gpath.map_parent_id)
    for k in collect(keys(ARR)); k[1] < key[1] && delete!(ARR, k); end   # solo el paso en curso
    list = get!(ARR, key, GraphPath.GPath[])
    isempty(list) && push!(list, deepcopy(gpath))                     # la primera llegada, aún sin unir
    push!(list, deepcopy(gin))
end

after_join(gpath) = haskey(ARR, (Int(gpath.current_step), gpath.map_parent_id)) &&
                    check_union(gpath, ARR[(Int(gpath.current_step), gpath.map_parent_id)])

@eval GraphPath function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
    Main.before_join(gpath, gpath_inmutable)
    if is_valid_join(gpath, gpath_inmutable)
        gpath_inmutable = deepcopy(gpath_inmutable)
        PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
        PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
        Main.after_join(gpath)
    end
end

# ---------------- comprobación ----------------

choice_steps(og) = [k for k in 0:og.nsteps-1 if length(unique(x.id for x in get(og.alive, k, SetPathNodesId()))) >= 2]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)

function pinned(g, Q)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(Q))
    return g2
end

function samplesQ(og)
    Qs = Vector{Vector{NodeId}}([NodeId[]])
    steps = choice_steps(og)
    isempty(steps) && return Qs
    for _ in 1:SAMPLES
        m = rand(RNG[], 1:min(2, length(steps)))
        push!(Qs, [rand(RNG[], map_nodes(og, s)) for s in shuffle(RNG[], steps)[1:m]])
    end
    return Qs
end

# La clave de una llegada en la fila ℓ: la máscara (de un solo bit) que llevan sus nodos.
arrival_bit(A, ℓ) = first(values(A.og.ntags))[ℓ + 1]

function check_union(J, arrivals)
    bump!(:joins)
    ℓ = J.og.krows - 1
    ℓ >= 0 || return
    for Q in samplesQ(J.og)
        J2 = pinned(J, Q)
        bump!(:pins)
        if !J2.is_valid
            bump!(:jdead); continue
        end
        og = J2.og
        byb = Dict{PG.Mask, Any}()
        for A in arrivals
            A2 = pinned(A, Q)
            byb[arrival_bit(A, ℓ)] = A2.is_valid ? A2.og : nothing
        end
        for (x, t) in og.ntags
            for (a, aog) in byb
                PG.has_key(t, ℓ, a) || continue
                bump!(:nodes)
                if aog === nothing
                    bump!(:adead); bump!(:pnode)
                elseif !PG.is_alive(aog, x)
                    bump!(:pnode)
                end
            end
        end
        for e in values(og.edges), (a, aog) in byb
            PG.has_key(e.tags, ℓ, a) || continue
            bump!(:edges)
            (aog !== nothing && PG.has_edge(aog, e.a, e.b)) || bump!(:pedge)
        end
        for t in get(og.alive, og.nsteps - 1, SetPathNodesId())
            bump!(:tops)
            a = og.ntags[t][ℓ + 1]
            aog = get(byb, a, nothing)
            (aog !== nothing && PG.is_alive(aog, t)) || bump!(:ptop)
        end
    end
end

# ---------------- corpus ----------------

const ONLY = Set(split(get(ENV, "PROBE_ONLY", ""), ","; keepempty = false))
const COLS = (:joins, :pins, :jdead, :tops, :ptop, :nodes, :pnode, :adead, :edges, :pedge)

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances"),
            joinpath(ROOT, "../../lean/improves_bin/cnf/crafted")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && f != "tseitin_petersen_H.cnf" && (isempty(ONLY) || f in ONLY) &&
                push!(files, joinpath(d, f))
        end
    end
    return files
end

function main()
    open(OUT, "w") do io
        println(io, "instance\t" * join(string.(COLS), "\t") * "\tbits\ttime")
        for path in corpus()
            name = basename(path)
            empty!(TOT); empty!(ARR); GraphPath.TAG_BITS_CUT[] = 0
            t = @elapsed try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(sprint(showerror, e))"); flush(io); continue
            end
            empty!(ARR); GC.gc()
            println(io, "$name\t" * join([string(get(TOT, c, 0)) for c in COLS], "\t") *
                        "\t$(GraphPath.TAG_BITS_CUT[])\t$(round(t, digits = 1))")
            flush(io)
        end
    end
end

main()
