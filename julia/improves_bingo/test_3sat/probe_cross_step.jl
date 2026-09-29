# El paso inductivo de CrossOneSide (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_cross_step.jl <salida.tsv>
#
# Entradas de cada línea = remitentes (copia antes del filtro). Para A, B entradas distintas del paso N, un grupo Q de
# cimas de A (misma (id, padre)) y una pareja y–w de B que no es de A dentro de SQ (vivos de A que posee alguna cima de
# Q): Ac = la entrada del paso N-1 cuya clave es el padre de las cimas de Q (su llegada trajo Q).
#   np; removed (y–w arista de Ac); absent; one_grp (y y w en la estrella de un mismo grupo de cimas de Ac);
#   one_free (y en ese grupo, con aristas de todas las entradas del paso N-1, la pareja tiene paso libre);
#   split (y y w solo en estrellas de grupos distintos de Ac); noAc (no se encontró Ac)

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const SENDER = Dict{Any, Any}()

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        key = (gpath.map_parent_id, Int(gpath.current_step))
        haskey($(SENDER), key) || ($(SENDER)[key] = deepcopy(gpath))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

alive(h) = [x for (_, xs) in h.og.alive for x in xs]
tops(h) = collect(get(h.og.alive, Int(h.current_step) - 1, SetPathNodesId()))
function groups_of(h)
    gr = Dict{Any, Vector{PathNodeId}}()
    for q in tops(h)
        push!(get!(gr, (q.id, q.parent_id), PathNodeId[]), q)
    end
    return gr
end
star(h, Q) = Set(z for z in alive(h) if any(q -> PG.has_edge(h.og, z, q), Q))

function judge(A, B, prev)
    oa = A.og; ob = B.og
    for ((_, pid), Q) in groups_of(A)
        SQ = star(A, Q)
        Ac = pid === nothing ? nothing : get(prev, pid, nothing)
        for (y, w) in keys(ob.edges)
            (y == w || !(y in SQ) || !(w in SQ) || PG.has_edge(oa, y, w)) && continue
            bump(:np)
            if Ac === nothing
                bump(:noAc); continue
            end
            if PG.has_edge(Ac.og, y, w)
                bump(:removed); continue
            end
            bump(:absent)
            grs = collect(values(groups_of(Ac)))
            both = [G for G in grs if (S = star(Ac, G); y in S && w in S)]
            if isempty(both)
                bump(:split)
            else
                bump(:one_grp)
                # paso libre en la estrella de ese grupo en Ac, con aristas de todas las entradas del paso anterior
                ogs = [p.og for p in values(prev)]
                adj(a, b) = any(o -> PG.has_edge(o, a, b), ogs)
                ok = any(both) do G
                    S = star(Ac, G)
                    any(0:Int(Ac.current_step)-1) do l
                        (l == y.id.step || l == w.id.step) && return false
                        all(r -> r.id.step != l || !(adj(y, r) && adj(w, r)), S)
                    end
                end
                ok && bump(:one_free)
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:np, :noAc, :removed, :absent, :one_grp, :one_free, :split)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDER)
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            bystep = Dict{Int, Dict{Any, Any}}()
            for ((k, st), g) in SENDER
                g.is_valid || continue
                bystep[st] = get(bystep, st, Dict{Any, Any}())
                bystep[st][k] = g
            end
            for (st, es) in bystep
                prev = get(bystep, st - 1, nothing)
                (prev === nothing || st < 3) && continue
                for A in values(es), B in values(es)
                    A === B && continue
                    judge(A, B, prev)
                end
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
