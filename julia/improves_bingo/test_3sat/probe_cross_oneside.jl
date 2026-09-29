# CrossOneSide en las entradas de la línea (29-sept-2026, rama reader-stuck; sonda rápida, PROBE_ONLY pequeño).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_cross_oneside.jl <salida.tsv>
#
# Las entradas de cada línea se recogen como remitentes (copia antes del filtro de cada UP). Para cada par ordenado
# (A, B) de entradas distintas del mismo paso y cada grupo Q de cimas de A que comparten (id, padre) —los padres de un
# futuro hijo—, SQ = vivos de A que posee alguna cima de Q. Para cada pareja y–w con y, w ∈ SQ, arista de B y no de A:
# ¿hay un paso l (no el de y ni el de w) en el que ningún r ∈ SQ posee a y y a w por aristas de A ∪ B?
#   pairs (pares de entradas), groups, np (parejas), nf (sin paso libre: falla); all_: lo mismo con Q = todas las cimas
#   de A (SQ = todos los vivos de A)

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

function judge(A, B)
    oa = A.og; ob = B.og
    top = Int(A.current_step) - 1
    groups = Dict{Any, Vector{PathNodeId}}()
    for q in get(oa.alive, top, SetPathNodesId())
        push!(get!(groups, (q.id, q.parent_id), PathNodeId[]), q)
    end
    adj(a, b) = PG.has_edge(oa, a, b) || PG.has_edge(ob, a, b)
    # la versión con todas las cimas (prefijo all_): Q = todas las cimas de A
    allQ = collect(get(oa.alive, top, SetPathNodesId()))
    for (key, Q) in [collect(groups); [(:all, allQ)]]
        pre = key === :all ? "all_" : ""
        bump(Symbol(pre, "groups"))
        SQ = Set(z for z in alive(A) if any(q -> PG.has_edge(oa, z, q), Q))
        byl = Dict{Int, Vector{PathNodeId}}()
        for r in SQ
            push!(get!(byl, Int(r.id.step), PathNodeId[]), r)
        end
        for (y, w) in keys(ob.edges)
            (y == w || !(y in SQ) || !(w in SQ) || PG.has_edge(oa, y, w)) && continue
            bump(Symbol(pre, "np"))
            ok = any(0:top) do l
                (l == y.id.step || l == w.id.step) && return false
                all(r -> !(adj(y, r) && adj(w, r)), get(byl, l, PathNodeId[]))
            end
            ok || bump(Symbol(pre, "nf"))
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:pairs, :groups, :np, :nf, :all_groups, :all_np, :all_nf)
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
            bystep = Dict{Int, Vector{Any}}()
            for ((_, st), g) in SENDER
                push!(get!(bystep, st, Any[]), g)
            end
            for (_, gs) in bystep, A in gs, B in gs
                A === B && continue
                (A.is_valid && B.is_valid && A.current_step >= 2) || continue
                bump(:pairs)
                judge(A, B)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
