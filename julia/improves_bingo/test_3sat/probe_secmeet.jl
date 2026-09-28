# SecMeet: ¿la intersección de dos secciones es una sección del pin? (28-sept-2026; Lean SecInduction.lean)
#
#   julia --project=. test_3sat/probe_secmeet.jl <salida.tsv> [max_estados]
#
# El paso de la inducción para SecPair a lo largo del lector. En cada estado válido h del lector (DFS, hasta
# max_estados), para cada paso con elección k0 y cada nodo del mapa b de k0, con h' = el pin de b
# (GraphPath.filter!(copia, [b])), y para cada otro paso con elección k de h' y cada nodo del mapa b' de k:
#   A = S_b(h) ∩ S_b'(h)   (aristas de las dos secciones de h)
#   B = S_b'(h')           (la sección de b' recalculada en el pin)
# SecMeet: A ⊆ B.  meet_miss = aristas de A fuera de B (debería ser 0).  B ⊆ A se espera siempre: extra = B ∖ A.
# Con SecMeet (y PinEqSec), SecPair en h da SecPair en h' (SecInduction.lean, secPair_filterAll).

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const MAX_STATES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 150
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph

function sec_edges(adj)
    s = Set{Tuple{PathNodeId, PathNodeId}}()
    for (y, t) in adj, (_, ws) in t, w in ws
        w != y && haskey(adj, w) && push!(s, PG.edge_key(y, w))
    end
    return s
end

function sections(og, k)
    groups = Dict{NodeId, Vector{PathNodeId}}()
    for x in og.alive[k]
        push!(get!(groups, x.id, PathNodeId[]), x)
    end
    return Dict(b => sec_edges(GraphPath.sec_fix!(GraphPath.sec_section(og, xs), og.nsteps)) for (b, xs) in groups)
end

mutable struct Acc
    states :: Int; cmp :: Int; miss :: Int; miss_cases :: Int; extra :: Int; trunc :: Bool
end

function check_state!(acc, gpath)
    og = gpath.og
    steps = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
    secs = Dict(k => sections(og, k) for k in steps)
    for k0 in steps, (b, Sb) in secs[k0]
        g2 = deepcopy(gpath)
        GraphPath.filter!(g2, SetNodesId([b]))
        g2.is_valid || continue
        for k in steps
            k == k0 && continue
            GraphPath.choice_at(g2.og, k) || continue
            secs2 = sections(g2.og, k)
            for (b2, Sb2) in secs[k]
                A = intersect(Sb, Sb2)
                B = get(secs2, b2, Set{Tuple{PathNodeId, PathNodeId}}())
                acc.cmp += 1
                m = length(setdiff(A, B))
                acc.miss += m
                m > 0 && (acc.miss_cases += 1)
                acc.extra += length(setdiff(B, A))
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
        println(io, "instance\tstates\tcmp\tmeet_miss\tmiss_cases\textra\ttrunc")
        for path in corpus()
            name = basename(path)
            acc = Acc(0, 0, 0, 0, 0, false)
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
            println(io, "$name\t$(acc.states)\t$(acc.cmp)\t$(acc.miss)\t$(acc.miss_cases)\t$(acc.extra)\t$(acc.trunc)")
            flush(io)
        end
    end
end

main()
