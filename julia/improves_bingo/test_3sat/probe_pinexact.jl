# Confluencia del review y PinExact (28-sept-2026; plan para ReviewExact).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_pinexact.jl <salida.tsv> [muestras] [semilla]
#
# La máquina paso a paso; en cada gpath válido de la línea (tras los joins), `muestras` veces cada medida:
#   Confluencia: dos nodos del mapa b1, b2 de pasos con elección distintos (al azar). Se comparan
#     pin(pin(g, b1), b2), pin(pin(g, b2), b1) y pin(g, [b1, b2]) (GraphPath.filter!, con su review):
#     conf_bad = alguna de las tres difiere en validez, vivos o aristas.
#   PinExact: un conjunto P de 1 a 3 nodos del mapa en pasos con elección distintos (al azar); si pin(g, P) es
#     válido, EdgeClique en él (GraphPath.edge_clique_miss): pe_fail = alguna arista o nodo sin cubrir,
#     pe_trunc = demasiadas camarillas para juzgar.
# Por instancia: states, conf (comparaciones), conf_bad, pe (pins válidos juzgados), pe_fail, pe_dead (pins
# inválidos), pe_trunc.

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 3
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

line(machine) = (gs = GPath[]; CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step,
                                                                  g -> push!(gs, g)); gs)

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in og.alive[k]), by = n -> n.index)
pin(g, reqs) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(reqs)); g2)

same(a, b) = a.is_valid == b.is_valid &&
    (!a.is_valid || (GraphPath.alive_ids(a) == GraphPath.alive_ids(b) && Set(keys(a.og.edges)) == Set(keys(b.og.edges))))

mutable struct Acc
    states :: Int; conf :: Int; conf_bad :: Int; pe :: Int; pe_fail :: Int; pe_dead :: Int; pe_trunc :: Int
end

function check!(acc, rng, g)
    acc.states += 1
    steps = choice_steps(g.og)
    length(steps) >= 1 || return
    for _ in 1:SAMPLES
        if length(steps) >= 2
            k1, k2 = shuffle(rng, steps)[1:2]
            b1 = rand(rng, map_nodes(g.og, k1)); b2 = rand(rng, map_nodes(g.og, k2))
            a = pin(pin(g, [b1]), [b2]); b = pin(pin(g, [b2]), [b1]); c = pin(g, [b1, b2])
            acc.conf += 1
            (same(a, b) && same(a, c)) || (acc.conf_bad += 1)
        end
        m = rand(rng, 1:min(3, length(steps)))
        ks = shuffle(rng, steps)[1:m]
        P = [rand(rng, map_nodes(g.og, k)) for k in ks]
        h = pin(g, P)
        if !h.is_valid
            acc.pe_dead += 1
            continue
        end
        r = GraphPath.edge_clique_miss(h)
        if r === nothing
            acc.pe_trunc += 1
        else
            acc.pe += 1
            r == (0, 0) || (acc.pe_fail += 1)
        end
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
        println(io, "instance\tstates\tconf\tconf_bad\tpe\tpe_fail\tpe_dead\tpe_trunc")
        for path in corpus()
            name = basename(path)
            acc = Acc(0, 0, 0, 0, 0, 0, 0)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.init!(machine)
                end
                while true
                    for g in line(machine)
                        g.is_valid && check!(acc, rng, g)
                    end
                    (!SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)) || break
                    redirect_stdout(devnull) do
                        SatMachine.make_step!(machine)
                    end
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t$(acc.states)\t$(acc.conf)\t$(acc.conf_bad)\t$(acc.pe)\t$(acc.pe_fail)\t$(acc.pe_dead)\t$(acc.pe_trunc)")
            flush(io)
        end
    end
end

main()
