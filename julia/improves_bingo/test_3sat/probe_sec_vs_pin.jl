# ¿La sección de b es lo que deja el pin de b? (28-sept-2026; SecPair.lean, graph_path_secpair.jl)
#
#   julia --project=. test_3sat/probe_sec_vs_pin.jl <salida.tsv> [max_estados]
#
# En cada estado válido del lector (DFS por todas sus ramas, como probe_tri_sec.jl, hasta max_estados) y en
# cada paso k con elección, para cada nodo del mapa b de k se comparan:
#   P   — las aristas del estado tras el pin (GraphPath.filter!(copia, [b]), el review entero), vacío si muere;
#   Sec — las aristas de la sección de b (sec_fix!(sec_section(og, vivos de b))), la mayor SecClosed de b.
# P está cerrado por parejas y anclado en b, así que se espera P ⊆ Sec. La pregunta es si Sec = P.
#
# Por instancia:
#   cmp        — comparaciones (estado, k, b)
#   equal      — Sec = P
#   sec_bigger — P ⊊ Sec; extra = aristas de Sec fuera de P (suma), extra_nodes = nodos de Sec fuera de P
#   sec_miss   — aristas de P fuera de Sec (debería ser 0)
#   dead_nonempty — el pin muere y Sec no está vacía;  live_empty — el pin vive y Sec está vacía

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const MAX_STATES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 300
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
key2(a, b) = PG.edge_key(a, b)

edge_set(og) = Set(keys(og.edges))

function sec_edges(adj)
    s = Set{Tuple{PathNodeId, PathNodeId}}()
    for (y, t) in adj, (_, ws) in t, w in ws
        w != y && haskey(adj, w) && push!(s, key2(y, w))
    end
    return s
end

mutable struct Acc
    cmp :: Int; equal :: Int; bigger :: Int; extra :: Int; extra_nodes :: Int; miss :: Int
    dead_nonempty :: Int; live_empty :: Int; states :: Int; trunc :: Bool
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
            S = sec_edges(adj)
            g2 = deepcopy(gpath)
            GraphPath.filter!(g2, SetNodesId([b]))
            live = g2.is_valid
            P = live ? edge_set(g2.og) : Set{Tuple{PathNodeId, PathNodeId}}()
            acc.cmp += 1
            !live && !isempty(adj) && (acc.dead_nonempty += 1)
            live && isempty(adj) && (acc.live_empty += 1)
            miss = length(setdiff(P, S))
            acc.miss += miss
            if S == P
                acc.equal += 1
            elseif miss == 0
                acc.bigger += 1
                acc.extra += length(setdiff(S, P))
                pn = live ? GraphPath.alive_ids(g2) : SetPathNodesId()
                acc.extra_nodes += count(y -> !(y in pn), keys(adj))
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
        println(io, "instance\tstates\tcmp\tequal\tsec_bigger\textra\textra_nodes\tsec_miss\tdead_nonempty\tlive_empty\ttrunc")
        for path in corpus()
            name = basename(path)
            acc = Acc(0, 0, 0, 0, 0, 0, 0, 0, 0, false)
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
            println(io, "$name\t$(acc.states)\t$(acc.cmp)\t$(acc.equal)\t$(acc.bigger)\t$(acc.extra)\t" *
                        "$(acc.extra_nodes)\t$(acc.miss)\t$(acc.dead_nonempty)\t$(acc.live_empty)\t$(acc.trunc)")
            flush(io)
        end
    end
end

main()
