# ¿Son cerradas las intersecciones de piezas de dos filas? (29-sept-2026, rama row-tags; docs/plans/lean_row_tags.md,
# «Estado»). La regla de la etiqueta cierra cada pieza (ℓ, a) por separado. La demostración del veredicto necesita,
# al bajar por la línea, que la pieza de la cima en una fila vuelva a partirse en la fila de abajo dentro de ella:
# que la intersección (ℓ₂, a) ∩ (ℓ₁, b) sea cerrada, en los estados que visita el lector (fijados y revisados).
#
#   PROBE_MAP=bin ROW_TAGS=on test_3sat/run_capped.sh <tope_MB> <tope_s> julia --heap-size-hint=<G> --project=. \
#       test_3sat/probe_row_tags_nested.jl <salida.tsv> [max_estados] [max_pares_de_filas]
#
# Para cada estado visitado por el lector (todas sus ramas, hasta max_estados) y cada par de filas mezcladas
# ℓ₁ < ℓ₂ (hasta max_pares_de_filas por estado) y claves a (en ℓ₂), b (en ℓ₁): I = los nodos y aristas que llevan
# a en ℓ₂ y b en ℓ₁. Se comprueba con las mismas condiciones que la regla (vecino en cada paso, testigo común en
# cada paso, padre e hijo dentro) y se calcula su mayor subconjunto cerrado.
#   inter      — intersecciones no vacías miradas
#   open       — intersecciones que no son cerradas tal cual
#   nlost      — nodos que pierde I hasta su punto fijo (suma)
#   tops       — cimas en alguna intersección; tlost — cimas que salen del punto fijo de alguna intersección
#   tdead      — cimas que salen del punto fijo de todas sus intersecciones, contando cualquier par de filas
#   pdead      — pares (cima, par de filas) en que la cima está en alguna intersección de esas dos filas y sale del
#                punto fijo de todas: para ese par de filas no tiene ninguna estructura anidada. Es el caso que
#                rompería la bajada; tpd — cimas con algún par así
# Con PROBE_ONLY=a.cnf,b.cnf solo esas instancias.

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const MAX_STATES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 30
const MAX_PAIRS = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 400
include(joinpath(ROOT, "src/main.jl"))

PathOwnersGraph.tags_on() || error("esta sonda necesita ROW_TAGS=on")
const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const FIRST_LIT = get(ENV, "PROBE_MAP", "bin") == "bin" ? Step(1) : Step(0)
const TOT = Dict{Symbol, Int}()
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

# La intersección como pieza (mismo formato que GraphPath.tag_sub), restringida a los nodos de `keep`.
function inter_sub(og, ℓ2, a, ℓ1, b, keep)
    sub = GraphPath.TagSub()
    for (x, t) in og.ntags
        (x in keep && PG.has_key(t, ℓ2, a) && PG.has_key(t, ℓ1, b)) || continue
        sub[x] = Dict(Int(x.id.step) => SetPathNodesId([x]))
    end
    for e in values(og.edges)
        (PG.has_key(e.tags, ℓ2, a) && PG.has_key(e.tags, ℓ1, b)) || continue
        sa = get(sub, e.a, nothing); sb = get(sub, e.b, nothing)
        (sa === nothing || sb === nothing) && continue
        push!(get!(sa, Int(e.b.id.step), SetPathNodesId()), e.b)
        push!(get!(sb, Int(e.a.id.step), SetPathNodesId()), e.a)
    end
    return sub
end

# El mayor subconjunto de nodos de I que se sostiene (las aristas que fallan se quitan de la pieza en cada vuelta).
function fixpoint(gpath, ℓ2, a, ℓ1, b)
    og = gpath.og
    keep = Set(keys(og.ntags))
    sub = inter_sub(og, ℓ2, a, ℓ1, b, keep)
    start = Set(keys(sub))
    isempty(start) && return (start, start, true)
    closed = true
    while true
        bad_nodes = [x for x in keys(sub) if !GraphPath.tag_node_keeps(gpath, sub, x)]
        bad_edges = Tuple{PathNodeId, PathNodeId}[]
        for (x, d) in sub, (_, ws) in d, w in ws
            (w != x && PG.node_ord(x) < PG.node_ord(w)) || continue
            GraphPath.tag_edge_keeps(gpath, sub, x, w) || push!(bad_edges, (x, w))
        end
        isempty(bad_nodes) && isempty(bad_edges) && break
        closed = false
        for x in bad_nodes
            delete!(sub, x)
        end
        for (x, d) in sub, (_, ws) in d
            filter!(w -> w == x || haskey(sub, w), ws)
        end
        for (x, w) in bad_edges
            haskey(sub, x) && (s = get(sub[x], Int(w.id.step), nothing); s === nothing || delete!(s, w))
            haskey(sub, w) && (s = get(sub[w], Int(x.id.step), nothing); s === nothing || delete!(s, x))
        end
    end
    return (start, Set(keys(sub)), closed)
end

function check_state!(gpath)
    og = gpath.og
    rows = GraphPath.tag_mixed_rows(og)
    length(rows) >= 2 || return
    top = og.nsteps - 1
    tops_in = Set{PathNodeId}(); tops_ok = Set{PathNodeId}(); tops_pd = Set{PathNodeId}()
    npairs = 0
    for i in length(rows):-1:2, j in i-1:-1:1
        npairs >= MAX_PAIRS && break
        npairs += 1
        ℓ2, ℓ1 = rows[i], rows[j]
        k2 = PG.NOKEY; k1 = PG.NOKEY
        for t in values(og.ntags); k2 |= t[ℓ2 + 1]; k1 |= t[ℓ1 + 1]; end
        pin = Set{PathNodeId}(); pok = Set{PathNodeId}()
        for a in GraphPath.bits_of(k2), b in GraphPath.bits_of(k1)
            start, fin, closed = fixpoint(gpath, ℓ2, a, ℓ1, b)
            isempty(start) && continue
            bump!(:inter)
            closed || bump!(:open)
            bump!(:nlost, length(start) - length(fin))
            for x in start
                Int(x.id.step) == top || continue
                push!(tops_in, x); push!(pin, x)
                x in fin ? (push!(tops_ok, x); push!(pok, x)) : bump!(:tlost)
            end
        end
        dead = setdiff(pin, pok)
        bump!(:pdead, length(dead))
        union!(tops_pd, dead)
    end
    bump!(:tpd, length(tops_pd))
    bump!(:tops, length(tops_in))
    bump!(:tdead, length(setdiff(tops_in, tops_ok)))
    bump!(:states)
end

is_end(node) = contains(node.title, "or") || contains(node.title, "FusionNode")
const SEEN = Ref(0)

function dfs!(gpath, step)
    SEEN[] >= MAX_STATES && return
    SEEN[] += 1
    check_state!(gpath)
    ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
    isempty(ids) && return
    is_end(PathCollectionLines.get_node(gpath.table_lines, first(ids))) && return
    for b in sort(unique(x.id for x in ids), by = n -> n.index)
        g2 = deepcopy(gpath)
        GraphPath.filter!(g2, SetNodesId([b]))
        g2.is_valid || continue
        dfs!(g2, step + 2)
    end
end

const ONLY = Set(split(get(ENV, "PROBE_ONLY", ""), ","; keepempty = false))
const COLS = (:states, :inter, :open, :nlost, :tops, :tlost, :tdead, :pdead, :tpd)

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
        println(io, "instance\t" * join(string.(COLS), "\t") * "\ttime")
        for path in corpus()
            name = basename(path)
            empty!(TOT); SEEN[] = 0
            t = @elapsed try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
                if SatMachine.have_solution(machine)
                    g0 = deepcopy(first(SatMachine.get_gpath_solutions(machine)))
                    g0.review_owners = true
                    GraphPath.make_review_owners!(g0)
                    g0.is_valid && dfs!(g0, FIRST_LIT)
                end
            catch e
                println(io, "$name\tERROR $(sprint(showerror, e))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(get(TOT, c, 0)) for c in COLS], "\t") * "\t$(round(t, digits = 1))")
            flush(io)
        end
    end
end

main()
