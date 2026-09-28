# SecInPin: ¿por qué sobrevive la sección de b al review del pin de b? (28-sept-2026; SecPair.lean)
#
#   julia --project=. test_3sat/probe_secinpin.jl <salida.tsv> [max_estados]
#
# En cada estado válido del lector (DFS por todas sus ramas, hasta max_estados) y en cada paso k con elección, para
# cada nodo del mapa b de k, con S = la sección de b (GraphPath.sec_fix!(sec_section(...))):
#
# 1. Qué corta el review del pin (GraphPath.filter!(copia, [b])), por regla (PathOwnersGraph.REMOVED_BY):
#    cut_clean, cut_pair, cut_parents, cut_sons (aristas quitadas), links (LINK_PRUNED).
#    s_hit: aristas de S que el pin no conserva (0 si la sección sobrevive).
# 2. Si S está cerrada por las reglas de estructura, en el estado antes del pin:
#    link_fail    — nodo de S (no raíz) sin padre enlazado en S, o (no cima) sin hijo enlazado en S;
#    par_fail     — arista (x,w) de S sin padre p de x (enlazado, en S) con p = w o (p,w) en S;
#    son_fail     — lo mismo con los hijos.
#    Si las tres son 0, S es una estructura cerrada por todas las reglas del review (parejas por construcción),
#    y SecInPin sería la generalización de carried_review de una camarilla a una sección.

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const MAX_STATES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 300
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const RULES = (:clean, :pair, :parents, :sons)

sec_nodes(adj) = Set(y for (y, t) in adj if any(ws -> any(w -> w != y, ws), values(t)))
sec_adj(adj, y, w) = y == w ? haskey(adj, y) : GraphPath.sec_has(adj, y, w)

mutable struct Acc
    cmp :: Int; states :: Int; trunc :: Bool
    cut :: Dict{Symbol, Int}; links :: Int; s_hit :: Int
    link_fail :: Int; par_fail :: Int; son_fail :: Int
end
Acc() = Acc(0, 0, false, Dict(r => 0 for r in RULES), 0, 0, 0, 0, 0)

function structure_fails!(acc, gpath, adj)
    nodes = sec_nodes(adj)
    top = gpath.current_step - 1
    for y in nodes
        n = PathCollectionLines.get_node(gpath.table_lines, y)
        n === nothing && (acc.link_fail += 1; continue)
        is_root = y.parent_id === nothing
        is_top = y.id.step == top
        ok_p = is_root || any(p -> p in nodes && sec_adj(adj, y, p), n.parents)
        ok_s = is_top || any(s -> s in nodes && sec_adj(adj, y, s), n.sons)
        (ok_p && ok_s) || (acc.link_fail += 1)
    end
    for (y, t) in adj, (_, ws) in t, w in ws
        (w == y || !(y in nodes) || !(w in nodes)) && continue
        n = PathCollectionLines.get_node(gpath.table_lines, y)
        n === nothing && continue
        if y.parent_id !== nothing
            any(p -> p in nodes && sec_adj(adj, p, w), n.parents) || (acc.par_fail += 1)
        end
        if y.id.step != top
            any(s -> s in nodes && sec_adj(adj, s, w), n.sons) || (acc.son_fail += 1)
        end
    end
end

function compare_state!(acc, gpath)
    og = gpath.og
    for k in 0:og.nsteps-1
        GraphPath.choice_at(og, k) || continue
        groups = Dict{NodeId, Vector{PathNodeId}}()
        for x in og.alive[k]
            push!(get!(groups, x.id, PathNodeId[]), x)
        end
        for (b, xs) in groups
            adj = GraphPath.sec_fix!(GraphPath.sec_section(og, xs), og.nsteps)
            structure_fails!(acc, gpath, adj)
            before = Dict(r => get(PG.REMOVED_BY, r, 0) for r in RULES)
            l0 = GraphPath.LINK_PRUNED[]
            g2 = deepcopy(gpath)
            GraphPath.filter!(g2, SetNodesId([b]))
            for r in RULES
                acc.cut[r] += get(PG.REMOVED_BY, r, 0) - before[r]
            end
            acc.links += GraphPath.LINK_PRUNED[] - l0
            acc.cmp += 1
            for (y, t) in adj, (_, ws) in t, w in ws
                w == y && continue
                (g2.is_valid && PG.has_edge(g2.og, y, w)) || (acc.s_hit += 1)
            end
        end
    end
end

is_end(node) = contains(node.title, "or") || contains(node.title, "FusionNode")

function dfs!(acc, gpath, step)
    acc.states >= MAX_STATES && (acc.trunc = true; return)
    acc.states += 1
    compare_state!(acc, gpath)
    ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
    is_end(PathCollectionLines.get_node(gpath.table_lines, first(ids))) && return
    for b in sort(unique(x.id for x in ids), by = n -> n.index)
        g2 = deepcopy(gpath)
        GraphPath.filter!(g2, SetNodesId([b]))
        g2.is_valid && dfs!(acc, g2, step + 2)
    end
end

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
        println(io, "instance\tstates\tcmp\tcut_clean\tcut_pair\tcut_parents\tcut_sons\tlinks\ts_hit\t" *
                    "link_fail\tpar_fail\tson_fail\ttrunc")
        for path in corpus()
            name = basename(path)
            acc = Acc()
            try
                machine = SatMachine.new(GraphMap.load_import!(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
                SatMachine.have_solution(machine) &&
                    dfs!(acc, deepcopy(first(SatMachine.get_gpath_solutions(machine))), Step(0))
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            c = acc.cut
            println(io, "$name\t$(acc.states)\t$(acc.cmp)\t$(c[:clean])\t$(c[:pair])\t$(c[:parents])\t$(c[:sons])\t" *
                        "$(acc.links)\t$(acc.s_hit)\t$(acc.link_fail)\t$(acc.par_fail)\t$(acc.son_fail)\t$(acc.trunc)")
            flush(io)
        end
    end
end

main()
