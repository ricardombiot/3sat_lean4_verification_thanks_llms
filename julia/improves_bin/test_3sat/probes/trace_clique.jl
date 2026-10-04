# Traza de una clique concreta a lo largo de la máquina: por entradas (unión de la línea) y por estado.
#   julia --project=../.. trace_clique.jl f.cnf desde "k2.1__k1.0__k0.0" "k13.1__k12.0__k11.1" ...
include("./../../src/main.jl")
key(p) = Alias.as_key(p)
function nodes_of(g)
    out = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; out[pid] = node; end
    out
end
owns1(node, q) = haskey(node.owners.table, q.id.step) && (q in node.owners.table[q.id.step])
function test(sts, Q, s)
    cl = all(q -> all(t -> any(st -> haskey(st, q) && owns1(st[q], t), sts), Q), Q)
    miss = nothing
    for l in 0:s
        ok = any(st -> any(p -> p[1].id.step == l && all(q -> any(st2 -> haskey(st2, p[1]) && owns1(st2[p[1]], q), sts), Q), st), sts)
        if !ok; miss = l; break; end
    end
    (cl, miss)
end
function main(args)
    gmap = GraphMapBin.load_import_bin!(args[1]); from = parse(Int, args[2]); keys_ = args[3:end]
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while true
        s = m.current_step
        gps = []; CollectionTimeline.for_each_gpath(m.timeline, s, g -> push!(gps, g))
        sts = [nodes_of(g) for g in gps]
        if s >= from
            allp = Set(p for st in sts for p in keys(st))
            Q = [p for p in allp if key(p) in keys_]
            if length(Q) < length(keys_)
                println("paso $s: algún miembro ya no existe ($(length(Q))/$(length(keys_)))")
            else
                println("paso $s: por entradas $(test(sts, Q, s))  por estado " *
                        join(["$(g.map_parent_id.step).$(g.map_parent_id.index)=$(test([st], Q, s))" for (g, st) in zip(gps, sts)], " "))
            end
        end
        (SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m)) && break
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
    println("fin: sat=$(SatMachine.have_solution(m))")
end
main(ARGS)
