# ¿Es SecPair una propiedad del review en cualquier estado fijado, o solo de los estados del lector?
# (28-sept-2026; tras SecMeet FALSO, SecInduction.lean)
#
#   julia --project=. test_3sat/probe_secpair_anypin.jl <salida.tsv> [recorridos] [semilla] [map|node]
#
# grain = map (por defecto): cada pin es un nodo del mapa b (GraphPath.filter!(g, [b]), como el lector).
# grain = node: cada pin es un nodo del camino x: los demás vivos de su paso salen del grafo (como hace
#   filter_require! con los de otro nodo del mapa) y se vuelve a pasar el review entero (make_review_owners!).
#
# Desde el estado final de la máquina, `recorridos` paseos al azar (semilla fija). En cada estado válido:
#   · se comprueba SecPair y SecPairX (GraphPath.sec_pair_bad, by = :map / :node);
#   · se elige al azar un paso con elección k (cualquiera, no solo los de literal) y se prueban todos sus nodos del
#     mapa: dead_end si todos dejan el gpath inválido;
#   · se sigue por un pin válido al azar; uno de cada tres movimientos fija además otro nodo del mapa de otro paso
#     con elección, a la vez (GraphPath.filter!(g, [b, b2])); si ese doble pin muere, se queda el simple.
# Por instancia: states, sp_fail / spx_fail (estados donde falla SecPair / SecPairX), bad (aristas fuera de toda
# sección), pins, dead_pins, dead_ends, double (dobles pins válidos).

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const WALKS = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 30
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
const GRAIN = length(ARGS) >= 4 ? Symbol(ARGS[4]) : :map
include(joinpath(ROOT, "src/main.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

mutable struct Acc
    states :: Int; sp_fail :: Int; spx_fail :: Int; bad :: Int
    pins :: Int; dead_pins :: Int; dead_ends :: Int; double :: Int
end

# Pasos con elección y candidatos a pin, según el grano.
choice_steps(og) = GRAIN == :map ? [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)] :
                                   [k for k in 0:og.nsteps-1 if length(og.alive[k]) >= 2]
map_nodes(og, k) = GRAIN == :map ? sort(unique(x.id for x in og.alive[k]), by = n -> n.index) :
                                   sort(collect(og.alive[k]), by = x -> PathOwnersGraph.node_ord(x))

function pinned(g, reqs)
    g2 = deepcopy(g)
    if GRAIN == :map
        GraphPath.filter!(g2, SetNodesId(reqs))
    else
        for x in reqs, y in collect(g2.og.alive[x.id.step])
            y == x && continue
            GraphPath.remove_node_owner!(g2, y; rule = :pin)
            g2.review_owners = true
        end
        GraphPath.make_review_owners!(g2)
    end
    return g2
end

function check!(acc, g)
    acc.states += 1
    bad = GraphPath.sec_pair_bad(g.og; by = :map)
    badx = GraphPath.sec_pair_bad(g.og; by = :node)
    isempty(bad) || (acc.sp_fail += 1)
    isempty(badx) || (acc.spx_fail += 1)
    acc.bad += length(bad)
end

function walk!(acc, rng, g)
    move = 0
    while true
        check!(acc, g)
        steps = choice_steps(g.og)
        isempty(steps) && return
        k = rand(rng, steps)
        live = Tuple{Any, Any}[]
        for b in map_nodes(g.og, k)
            acc.pins += 1
            g2 = pinned(g, [b])
            g2.is_valid ? push!(live, (b, g2)) : (acc.dead_pins += 1)
        end
        isempty(live) && (acc.dead_ends += 1; return)
        b, next = rand(rng, live)
        move += 1
        if move % 3 == 0
            others = [k2 for k2 in steps if k2 != k]
            if !isempty(others)
                k2 = rand(rng, others)
                b2 = rand(rng, map_nodes(g.og, k2))
                g3 = pinned(g, [b, b2])
                g3.is_valid && (acc.double += 1; next = g3)
            end
        end
        g = next
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
    rng = MersenneTwister(SEED)
    open(OUT, "w") do io
        println(io, "instance\tstates\tsp_fail\tspx_fail\tbad\tpins\tdead_pins\tdead_ends\tdouble")
        for path in corpus()
            name = basename(path)
            acc = Acc(0, 0, 0, 0, 0, 0, 0, 0)
            try
                machine = SatMachine.new(GraphMap.load_import!(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
                if SatMachine.have_solution(machine)
                    g0 = first(SatMachine.get_gpath_solutions(machine))
                    for _ in 1:WALKS
                        walk!(acc, rng, deepcopy(g0))
                    end
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t$(acc.states)\t$(acc.sp_fail)\t$(acc.spx_fail)\t$(acc.bad)\t$(acc.pins)\t" *
                        "$(acc.dead_pins)\t$(acc.dead_ends)\t$(acc.double)")
            flush(io)
        end
    end
end

main()
