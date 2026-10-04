# Etiquetas por fila con review por etiqueta (ROW_TAGS; src/graph_path/graph_path_tags.jl) contra el exhaustivo
# (29-sept-2026, rama row-tags, informe v204 §7.7 pasos 1–2). Mismo arnés que probe_star_rule.jl: máquina entera y
# lector en todas sus ramas.
#
#   PROBE_MAP=bin ROW_TAGS=<off|on> test_3sat/run_capped.sh <tope_MB> <tope_s> julia --heap-size-hint=<G> \
#       --project=. test_3sat/probe_row_tags.jl <base|tags> <salida.tsv> [max_estados]
#
# El modo lo fija la variable ROW_TAGS antes de cargar (base ⇒ :off, tags ⇒ :on); el script comprueba que coincide.
# Columnas: verdict, truth; time; bits (claves quitadas), tedges, tnodes (aristas y nodos muertos por la regla);
# states, pins, dead_pins, dead_ends; leaves, leaves_ok, nsols; trunc; edges (del gpath final); live_mb (heap vivo
# tras la instancia); maxrss_mb (máximo del proceso hasta ahí). Con PROBE_ONLY=a.cnf,b.cnf solo esas instancias.

const ROOT = abspath(joinpath(@__DIR__, ".."))
const MODE = Symbol(ARGS[1])
const OUT = abspath(ARGS[2])
const MAX_STATES = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 4000
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
# En el mapa bin los literales están en los pasos impares (fusión raíz en el paso 0; PathReader.new).
const FIRST_LIT = get(ENV, "PROBE_MAP", "bin") == "bin" ? Step(1) : Step(0)
step_of(x) = x.id.step

PathOwnersGraph.ROW_TAGS[] == (MODE == :tags ? :on : :off) || error("ROW_TAGS=$(PathOwnersGraph.ROW_TAGS[]) no casa con el modo $MODE")

function tri_ok(og, x, y, w)
    iy = og.inc[y]; iw = og.inc[w]
    for (l, xs) in og.inc[x]
        ys = get(iy, l, nothing); ws = get(iw, l, nothing)
        (ys === nothing || ws === nothing) && continue
        any(r -> r in ys && r in ws, xs) || return false
    end
    return true
end

# ---------------- el lector en todas sus ramas ----------------

mutable struct Stats
    states :: Int; pins :: Int; dead_pins :: Int; dead_ends :: Int
    leaves :: Vector{String}; trunc :: Bool
end

is_end(node) = contains(node.title, "or") || contains(node.title, "FusionNode")

function dfs!(st, gpath, step, bits)
    st.states >= MAX_STATES && (st.trunc = true; return)
    st.states += 1
    ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
    node = PathCollectionLines.get_node(gpath.table_lines, first(ids))
    if is_end(node)
        push!(st.leaves, join(Int.(bits)))
        return
    end
    alive = 0
    for b in sort(unique(x.id for x in ids), by = n -> n.index)
        st.pins += 1
        g2 = deepcopy(gpath)
        GraphPath.filter!(g2, SetNodesId([b]))
        if !g2.is_valid
            st.dead_pins += 1
            continue
        end
        alive += 1
        dfs!(st, g2, step + 2, vcat(bits, b.index))
    end
    alive == 0 && (st.dead_ends += 1)
end

# Tríos que se poseen dos a dos y no comparten entrada en algún paso (cada trío una vez).
function trifail(og)
    n = 0
    for e in values(og.edges), x in PG.neighbors_all(og, e.a)
        (x == e.a || x == e.b || !PG.has_edge(og, x, e.b)) && continue
        PG.node_ord(x) > PG.node_ord(e.b) || continue          # x el mayor de los tres
        tri_ok(og, x, e.a, e.b) || (n += 1)
    end
    return n
end

# ---------------- corpus

# Instancias que se saltan (separadas por comas en PROBE_SKIP), p. ej. tseitin_petersen_H.cnf con tri/sec.
const SKIP = Set(split(get(ENV, "PROBE_SKIP", ""), ","; keepempty = false))
const ONLY = Set(split(get(ENV, "PROBE_ONLY", ""), ","; keepempty = false))

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances"),
            joinpath(ROOT, "../../lean/improves_bin/cnf/crafted")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && !(f in SKIP) && (isempty(ONLY) || f in ONLY) && push!(files, joinpath(d, f))
        end
    end
    return files
end

# Las soluciones, del fichero del exhaustivo o corriéndolo.
function solutions(path)
    ex = replace(replace(path, "/instances/" => "/solver_exhaustive/"), ".cnf" => ".txt")
    if isfile(ex)
        ls = strip.(readlines(ex))
        return first(ls) == "SAT" ? Set(ls[2:end]) : Set{String}()
    end
    try
        s = ExhaustiveSolver.new(path); ExhaustiveSolver.run!(s)
        return Set(join(Int.(x)) for x in s.list_solutions)
    catch
        return nothing
    end
end

function main()
    files = corpus()
    open(OUT, "w") do io
        println(io, "instance\tverdict\ttruth\ttime\tbits\ttedges\ttnodes\tstates\tpins\tdead_pins\tdead_ends\tleaves\tleaves_ok\tnsols\ttrunc\tedges\tlive_mb\tmaxrss_mb")
        for path in files
            name = basename(path)
            sols = solutions(path)
            GraphPath.TAG_BITS_CUT[] = 0; GraphPath.TAG_EDGES_CUT[] = 0; GraphPath.TAG_NODES_CUT[] = 0
            local machine, t
            try
                machine = SatMachine.new(LOAD(path))
                t = @elapsed redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            sat = SatMachine.have_solution(machine)
            truth = sols === nothing ? "?" : string(!isempty(sols))
            st = Stats(0, 0, 0, 0, String[], false)
            ne, tf = 0, 0
            if sat
                og = first(SatMachine.get_gpath_solutions(machine)).og
                ne = length(og.edges)
            end
            if sat
                try
                    dfs!(st, deepcopy(first(SatMachine.get_gpath_solutions(machine))), FIRST_LIT, Int[])
                catch e
                    println(io, "$name\t$sat\t$truth\tREADER-ERROR $(sprint(showerror, e))"); flush(io); continue
                end
            end
            leaves = Set(st.leaves)
            ok = sols === nothing ? "?" : string(issubset(leaves, sols))
            nsols = sols === nothing ? "?" : string(length(sols))
            machine = nothing; GC.gc()
            live = round(Int, Base.gc_live_bytes() / 2^20); rss = round(Int, Sys.maxrss() / 2^20)
            println(io, "$name\t$sat\t$truth\t$(round(t, digits = 2))\t$(GraphPath.TAG_BITS_CUT[])\t" *
                        "$(GraphPath.TAG_EDGES_CUT[])\t$(GraphPath.TAG_NODES_CUT[])\t$(st.states)\t$(st.pins)\t" *
                        "$(st.dead_pins)\t$(st.dead_ends)\t$(length(leaves))\t$ok\t$nsols\t$(st.trunc)\t$ne\t$live\t$rss")
            flush(io)
        end
    end
end

main()
