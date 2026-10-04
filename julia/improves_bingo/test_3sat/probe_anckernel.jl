# AncKernel (28-sept-2026; lean/improves_bingo; argumento global de Absorb por cadenas).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_anckernel.jl <salida.tsv>
#
# Para un estado S: Anc(S) es el estado de ascendencia pura sobre los vivos de S — mismos vivos, enlaces = todos los
# pares compatibles (ids desplazados) entre vivos, aristas = los pares unidos por una cadena de enlaces entre vivos
# (z antepasado de x). AncKernel(S): el review de Anc(S) devuelve S.
#   states  — estados mirados (tras cada UP válido: `up`; tras cada join: `join`)
#   notanc  — aristas de S que no son de ascendencia (S ⊆ Anc(S) pide 0)
#   extra   — aristas del review de Anc(S) que S no tiene (AncKernel pide 0), bad — estados con extra > 0
#   missing — aristas de S que el review de Anc(S) quita, dead — Anc(S) revisado muere
# Columnas por tipo de estado: up_* y join_*.

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const TOT = Dict{Symbol, Int}()
const GMAP = Ref{Any}(nothing)
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

compat(p, y) = y.parent_id == p.id && y.gparent_id == p.parent_id && p.id.step + 1 == y.id.step

function anc_state(S)
    a = deepcopy(S)
    A = Set(GraphPath.alive_ids(a))
    byst = Dict{Int, Vector{PathNodeId}}()
    for x in A
        push!(get!(byst, x.id.step, PathNodeId[]), x)
    end
    par = Dict(x => [p for p in get(byst, x.id.step - 1, PathNodeId[]) if compat(p, x)] for x in A)
    son = Dict(x => [q for q in get(byst, x.id.step + 1, PathNodeId[]) if compat(x, q)] for x in A)
    PathCollectionLines.for_each(a.table_lines, function (node)
        if node.id in A
            empty!(node.parents); union!(node.parents, par[node.id])
            empty!(node.sons); union!(node.sons, son[node.id])
        end
    end)
    anc = Dict{PathNodeId, Set{PathNodeId}}()
    for st in sort(collect(keys(byst))), x in byst[st]
        s_ = Set{PathNodeId}()
        for p in par[x]
            push!(s_, p); union!(s_, anc[p])
        end
        anc[x] = s_
    end
    for k in collect(keys(a.og.edges))
        PG.remove_edge!(a.og, k[1], k[2]; rule = :anc)
    end
    for x in A, w in anc[x]
        PG.add_edge!(a.og, x, w)
    end
    return a, anc
end

function anckernel!(S, tag)
    bump!(Symbol(tag, "_states"))
    a, anc = anc_state(S)
    bump!(Symbol(tag, "_notanc"), count(k -> !(k[2] in anc[k[1]] || k[1] in anc[k[2]]), keys(S.og.edges)))
    a.review_owners = true
    a.is_valid = a.og.valid
    GraphPath.make_review_owners!(a)
    if !a.is_valid
        bump!(Symbol(tag, "_dead")); return
    end
    ex = count(k -> !haskey(S.og.edges, k), keys(a.og.edges))
    bump!(Symbol(tag, "_extra"), ex)
    ex > 0 && bump!(Symbol(tag, "_bad"))
    bump!(Symbol(tag, "_missing"), count(k -> !haskey(a.og.edges, k), keys(S.og.edges)))
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
            $(anckernel!)(gpath, "join")
        end
    end
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        gpath.is_valid && $(anckernel!)(gpath, "up")
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

const COLS = Tuple(Symbol(t, '_', c) for t in ("up", "join") for c in ("states", "notanc", "bad", "extra", "missing", "dead"))

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
