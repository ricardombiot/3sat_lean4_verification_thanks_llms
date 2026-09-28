# Sonda de las reglas 2 (tríos) y 3 (secciones por bit) de la propuesta para NoDeadEnd (28-sept-2026).
# Cada regla se mete en el review (se aplica hasta su punto fijo, junto con las de siempre) sin tocar
# src/: se redefine GraphPath.make_review_owners! desde aquí.
#
#   julia --project=. test_3sat/probe_tri_sec.jl <modo> <salida.tsv> [max_estados]
#
# modo:
#   base — el review de siempre.
#   tri  — regla 2, versión sólida: la arista (y,w) sobrevive si en cada paso m hay un x vivo que posee a
#          los dos y tal que x, y, w comparten entrada en cada paso. (La versión de §4.4, «se corta (y,w) si
#          un x cualquiera no comparte», pierde soluciones cuando x no está en ellas; no se mide.)
#   sec  — regla 3 (SecPair, §4.3; GraphPath.sec_pair_bad, espejo de SecPair.lean) a grano de mapa: para cada paso k con dos o más nodos del mapa y cada
#          nodo b del mapa en k, se restringe el grafo a lo compatible con b (aristas (y,w) con algún x de
#          b que posee a los dos) y se lleva a su punto fijo de la regla de parejas; la arista sobrevive
#          si está en alguna sección. Es la unión de las fijaciones de k, hecha en el review.
#   secx — como sec, con una sección por nodo del camino x de k (no por nodo del mapa): la camarilla de una
#          solución elige un x por paso, así que también es sólida, y no mezcla testigos de x distintos.
#
# Por instancia, la máquina entera con el modo y después el lector en todas sus ramas (DFS, cada rama un
# nodo del mapa del paso de literal, como PathExpReader), hasta max_estados:
#   verdict, truth           — veredicto de la máquina y del exhaustivo
#   cut                      — aristas quitadas por la regla nueva (en máquina y lector)
#   states, pins, dead_pins  — estados válidos del lector visitados, pins probados, pins que invalidan
#   dead_ends                — estados válidos en los que mueren todos los pins (lo que NoDeadEnd niega)
#   leaves, leaves_ok, nsols — hojas del lector, si son todas soluciones, y cuántas soluciones hay:
#                              sin truncar, leaves = nsols es que el lector no pierde ninguna
#   trunc                    — si el DFS se cortó por max_estados
#   edges, trifail           — en el gpath final (el que lee el lector): aristas, y tríos x, y, w que se
#                              poseen dos a dos sin entrada común en algún paso (fallos de TriPin, todo x)

const ROOT = abspath(joinpath(@__DIR__, ".."))
const MODE = Symbol(ARGS[1])
const OUT = abspath(ARGS[2])
const MAX_STATES = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 4000
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const CUT = Ref(0)
step_of(x) = x.id.step

# ---------------- regla 2: tríos (sólida) ----------------

# ¿Comparten x, y, w una entrada en cada paso?
function tri_ok(og, x, y, w)
    iy = og.inc[y]; iw = og.inc[w]
    for (l, xs) in og.inc[x]
        ys = get(iy, l, nothing); ws = get(iw, l, nothing)
        (ys === nothing || ws === nothing) && continue
        any(r -> r in ys && r in ws, xs) || return false
    end
    return true
end

# En cada paso m distinto de los de y y w (ahí basta x = y o x = w, que es la regla de parejas), algún
# x que posee a los dos cierra el trío.
function tri_edge_ok(og, y, w)
    for m in 0:og.nsteps-1
        (m == step_of(y) || m == step_of(w)) && continue
        ys = get(og.inc[y], m, nothing); ws = get(og.inc[w], m, nothing)
        (ys === nothing || ws === nothing) && return false
        any(x -> x in ws && tri_ok(og, x, y, w), ys) || return false
    end
    return true
end

tri_bad(og) = [(e.a, e.b) for e in values(og.edges) if !tri_edge_ok(og, e.a, e.b)]

# ---------------- regla 3: secciones (src/graph_path/graph_path_secpair.jl, espejo de SecPair.lean) ----------------

# ---------------- el review con la regla ----------------

# make_review_owners! se redefine, así que el review de siempre se copia aquí con otro nombre (el mismo
# cuerpo que src/graph_path/graph_path_filter.jl, sin CHECK_OG).
Core.eval(GraphPath, quote
    function base_review!(gpath :: GPath)
        if gpath.is_valid && gpath.review_owners
            REVIEW_ROUNDS[] += 1
            gpath.review_owners = false
            clean_invalid_nodes!(gpath)
            PAIR_MODE[] == :on && pair_consistency_after_clean!(gpath)
            LINK_MODE[] == :on && prune_stale_links!(gpath)
            review_owners_coherence_with_its_parents_sons!(gpath)
            LINK_MODE[] == :on && prune_stale_links!(gpath)
            gpath.review_owners && base_review!(gpath)
        end
    end
end)

extra_bad(og) = MODE == :tri ? tri_bad(og) : MODE == :sec ? GraphPath.sec_pair_bad(og; by = :map) :
                MODE == :secx ? GraphPath.sec_pair_bad(og; by = :node) : Tuple{PathNodeId, PathNodeId}[]

if MODE != :base
    Core.eval(GraphPath, quote
        function make_review_owners!(gpath :: GPath)
            base_review!(gpath)                          # las reglas de siempre, hasta su punto fijo
            while gpath.is_valid && gpath.table_lines.is_valid
                bad = $(extra_bad)(gpath.og)
                isempty(bad) && break
                for (a, b) in bad
                    PathOwnersGraph.remove_edge!(gpath.og, a, b; rule = $(QuoteNode(MODE)))
                end
                $(CUT)[] += length(bad)
                gpath.review_owners = true
                clean_invalid_nodes!(gpath)
                base_review!(gpath)
            end
        end
    end)
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

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances"),
            joinpath(ROOT, "../../lean/improves_bin/cnf/crafted")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && !(f in SKIP) && push!(files, joinpath(d, f))
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
        println(io, "instance\tverdict\ttruth\ttime\tcut\tstates\tpins\tdead_pins\tdead_ends\tleaves\tleaves_ok\tnsols\ttrunc\tedges\ttrifail")
        for path in files
            name = basename(path)
            sols = solutions(path)
            CUT[] = 0
            local machine, t
            try
                machine = SatMachine.new(GraphMap.load_import!(path))
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
                ne, tf = length(og.edges), trifail(og)
            end
            if sat
                try
                    dfs!(st, deepcopy(first(SatMachine.get_gpath_solutions(machine))), Step(0), Int[])
                catch e
                    println(io, "$name\t$sat\t$truth\tREADER-ERROR $(sprint(showerror, e))"); flush(io); continue
                end
            end
            leaves = Set(st.leaves)
            ok = sols === nothing ? "?" : string(issubset(leaves, sols))
            nsols = sols === nothing ? "?" : string(length(sols))
            println(io, "$name\t$sat\t$truth\t$(round(t, digits = 2))\t$(CUT[])\t$(st.states)\t$(st.pins)\t" *
                        "$(st.dead_pins)\t$(st.dead_ends)\t$(length(leaves))\t$ok\t$nsols\t$(st.trunc)\t$ne\t$tf")
            flush(io)
        end
    end
end

main()
