# Sonda de `ClauseKey` (lean/improves_bin, ClauseMixProbeMain.lean) en la máquina Julia.
#
#   julia --project=../.. clause_mix_probe.jl f.cnf v1 v2 v3
#
# Q = los nodos de camino de v1=1, v2=1, v3=1 (variables 1-indexadas, pasos positivos 2v-1).
# Tras cada paso de la máquina, en la línea actual:
#   * por entradas (`LineSem.Owns`: cada entrada puede venir de un estado distinto de la línea):
#     ¿Q es clique? ¿hay testigo (un nodo que posee todo Q) en cada paso 0..s?
#   * dentro de cada estado (`CertClique`): lo mismo en un solo gpath.
# Imprime el primer paso sin testigo y, la primera vez que un test pasa de sí a no, qué entradas faltan.

include("./../../src/main.jl")

key(p) = Alias.as_key(p)

function nodes_of(gpath)
    out = Dict{PathNodeId, Any}()
    for (_, line) in gpath.table_lines.table, (pid, node) in line.table
        out[pid] = node
    end
    out
end

owns(node, q) = haskey(node.owners.table, q.id.step) && (q in node.owners.table[q.id.step])

function line_test(states, Q, s)
    clique = all(q -> all(t -> any(st -> haskey(st, q) && owns(st[q], t), states), Q), Q)
    missing = nothing
    for l in 0:s
        found = false
        for st in states, (pid, node) in st
            pid.id.step == l || continue
            if all(q -> any(st2 -> haskey(st2, pid) && owns(st2[pid], q), states), Q)
                found = true; break
            end
        end
        if !found; missing = l; break; end
    end
    (clique, missing)
end

function state_test(st, Q, s)
    clique = all(q -> haskey(st, q) && all(t -> owns(st[q], t), Q), Q)
    missing = nothing
    for l in 0:s
        if !any(p -> p[1].id.step == l && all(q -> owns(p[2], q), Q), st)
            missing = l; break
        end
    end
    (clique, missing)
end

function main(args)
    path = args[1]
    vs = parse.(Int, args[2:4])
    gmap = GraphMapBin.load_import_bin!(path)
    machine = SatMachine.new(gmap)
    SatMachine.init!(machine)
    qsteps = [2v - 1 for v in vs]
    Qs = nothing
    println("stepCount=$(gmap.step)  pasos de Q=$(qsteps)")
    prev = Dict{Any, Any}()
    while true
        s = machine.current_step
        gps = []
        CollectionTimeline.for_each_gpath(machine.timeline, s, g -> push!(gps, g))
        states = [nodes_of(g) for g in gps]
        if Qs === nothing && s >= maximum(qsteps)
            cands = [unique([pid for st in states for pid in keys(st) if pid.id.step == qs && pid.id.index == 1]) for qs in qsteps]
            Qs = [[a, b, c] for a in cands[1] for b in cands[2] for c in cands[3]]
            println("candidatos Q: $(length(Qs))")
        end
        if Qs !== nothing
            for (i, Q) in enumerate(Qs)
                lt = line_test(states, Q, s)
                sts = [state_test(st, Q, s) for st in states]
                if lt[1]
                    keys_line = join(["$(g.map_parent_id.step).$(g.map_parent_id.index)" for g in gps], ",")
                    println("paso $s Q$i=$(map(key, Q))  por entradas: clique=$(lt[1]) falta testigo en $(lt[2])  " *
                            "por estado [$keys_line]: $(sts)")
                end
            end
        end
        (SatMachine.is_finished(machine) || !SatMachine.have_gpaths_step(machine)) && break
        redirect_stdout(devnull) do
            SatMachine.make_step!(machine)
        end
    end
    println("fin: soluciones=$(SatMachine.have_solution(machine))")
end

main(ARGS)
