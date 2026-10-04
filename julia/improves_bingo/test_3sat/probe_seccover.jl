# ¿Qué sección cubre una arista tras un pin? (28-sept-2026; tras SecMeet FALSO, SecInduction.lean)
#
#   julia --project=. test_3sat/probe_seccover.jl <salida.tsv> [max_estados]
#
# En cada estado válido h del lector (DFS, hasta max_estados), para cada paso con elección k0, cada nodo del mapa b
# de k0 con pin válido h' = filter!(copia, [b]), cada otro paso k con elección en h' y cada arista e de h':
#   cov_h   = nodos del mapa b'' de k con e en S_b''(h)
#   cov_h'  = nodos del mapa b'' de k con e en S_b''(h')
#   alive'  = nodos del mapa de k con vivos en h'
#   anch    = nodos del mapa b'' de k con un nodo x de b'' que posee a los dos extremos de e en h
# Cuenta, por arista (edges = total):
#   meet_fail   — cov_h ∩ alive' ⊄ cov_h' (algún b'' que la cubría y sigue vivo ya no la cubre): SecMeetAlive falla
#   dead_only   — los fallos de SecMeet se deben solo a b'' muertos: cov_h ∖ cov_h' ⊆ nodos muertos
#   cover_h_all — cov_h = anch (en h, toda ancla que posee los dos extremos la cubre)
#   cover_h'_all — cov_h' = anch' (lo mismo en h')
#   empty_h'    — cov_h' vacío (SecPair falla en h'; debería ser 0)

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const MAX_STATES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 60
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const EK = Tuple{PathNodeId, PathNodeId}

function sec_edges(adj)
    s = Set{EK}()
    for (y, t) in adj, (_, ws) in t, w in ws
        w != y && haskey(adj, w) && push!(s, PG.edge_key(y, w))
    end
    return s
end

function groups_at(og, k)
    groups = Dict{NodeId, Vector{PathNodeId}}()
    for x in og.alive[k]
        push!(get!(groups, x.id, PathNodeId[]), x)
    end
    return groups
end

sections(og, k) = Dict(b => sec_edges(GraphPath.sec_fix!(GraphPath.sec_section(og, xs), og.nsteps))
                       for (b, xs) in groups_at(og, k))

anchors(og, k, e) = Set(b for (b, xs) in groups_at(og, k)
                        if any(x -> PG.has_edge(og, x, e[1]) && PG.has_edge(og, x, e[2]), xs))

mutable struct Acc
    states :: Int; edges :: Int; meet_fail :: Int; dead_only :: Int; secmeet_fail :: Int
    cover_h_all :: Int; cover_h2_all :: Int; empty_h2 :: Int; trunc :: Bool
end

function check_state!(acc, gpath)
    og = gpath.og
    steps = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
    secs = Dict(k => sections(og, k) for k in steps)
    for k0 in steps, b in keys(groups_at(og, k0))
        g2 = deepcopy(gpath)
        GraphPath.filter!(g2, SetNodesId([b]))
        g2.is_valid || continue
        og2 = g2.og
        for k in steps
            (k == k0 || !GraphPath.choice_at(og2, k)) && continue
            secs2 = sections(og2, k)
            alive2 = Set(keys(groups_at(og2, k)))
            for e in keys(og2.edges)
                acc.edges += 1
                cov = Set(b2 for (b2, S) in secs[k] if e in S)
                cov2 = Set(b2 for (b2, S) in secs2 if e in S)
                isempty(cov2) && (acc.empty_h2 += 1)
                lost = setdiff(cov, cov2)
                if !isempty(lost)
                    acc.secmeet_fail += 1
                    issubset(intersect(cov, alive2), cov2) ? (acc.dead_only += 1) : (acc.meet_fail += 1)
                end
                cov == anchors(og, k, e) && (acc.cover_h_all += 1)
                cov2 == anchors(og2, k, e) && (acc.cover_h2_all += 1)
            end
        end
    end
end

is_end(node) = contains(node.title, "or") || contains(node.title, "FusionNode")

function dfs!(acc, gpath, step)
    acc.states >= MAX_STATES && (acc.trunc = true; return)
    acc.states += 1
    check_state!(acc, gpath)
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
        println(io, "instance\tstates\tedges\tsecmeet_fail\tdead_only\tmeet_fail\tcover_h_all\tcover_h2_all\tempty_h2\ttrunc")
        for path in corpus()
            name = basename(path)
            acc = Acc(0, 0, 0, 0, 0, 0, 0, 0, false)
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
            println(io, "$name\t$(acc.states)\t$(acc.edges)\t$(acc.secmeet_fail)\t$(acc.dead_only)\t$(acc.meet_fail)\t" *
                        "$(acc.cover_h_all)\t$(acc.cover_h2_all)\t$(acc.empty_h2)\t$(acc.trunc)")
            flush(io)
        end
    end
end

main()
