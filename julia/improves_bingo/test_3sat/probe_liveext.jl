# LiveExt en la línea (30-sept-2026, rama reader-stuck; lean LiveExt.lean).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_liveext.jl <salida.tsv> [tope]
#
# Con FORBID = :on (LIVE_FORBID=off: control sin tríos). Una cadena viva: de la cima hacia abajo, cada nodo padre vivo del anterior, vecinos dos a dos, sin
# trío prohibido. LiveExt: toda cadena viva que no ha llegado al paso 0 se alarga con un padre, viva.
# Se recorren por DFS todas las cadenas vivas de cada estado (hasta `tope` hojas por estado; `cap` cuenta los
# estados que lo alcanzan) y se cuentan los callejones (cadena viva sin alargar).
#   flt_*  — el remitente tras el filtro de requisitos del UP (un pin), antes de la fila nueva
#   arr_*  — llegadas (tras el UP y su review, punto :up_done)
#   join_* — uniones recién hechas (:join_post), sin revisar
#   jrev_* — las mismas uniones tras una revisión (lo que ve el siguiente UP y el lector)
#   fin_*  — estados finales revisados (reviewAll, el arranque del lector)
# Por grupo: states, chains (hojas completas), dead (callejones), dead_states, kmin (longitud de la cadena más corta
# atascada), cap.

using Random
const OUT = abspath(ARGS[1])
const CAP = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20000
const MODE = Symbol(get(ENV, "LIVE_FORBID", "on"))   # :off, control: sin tríos prohibidos
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b || PG.has_edge(g.og, a, b)
dead(g, a, b, r) = length(unique((a, b, r))) == 3 && PG.dead_trio(g.og, a, b, r)

function live_parents(g, x, chain)
    nd = PathCollectionLines.get_node(g.table_lines, x)
    nd === nothing && return PathNodeId[]
    [p for p in nd.parents if PG.is_alive(g.og, p) && all(w -> adj(g, w, p), chain) &&
        !any(dead(g, chain[i], chain[j], p) for i in eachindex(chain) for j in i+1:length(chain))]
end

function judge(g, pre)
    g.is_valid || return
    bump(Symbol(pre, "_states"))
    top = Int(g.current_step) - 1
    leaves = Ref(0); deads = Ref(0); kmin = Ref(typemax(Int))
    chain = PathNodeId[]
    function dfs(x)
        leaves[] > CAP && return
        push!(chain, x)
        s = Int(x.id.step)
        if s == 0
            leaves[] += 1
        else
            ps = live_parents(g, x, chain)
            if isempty(ps)
                deads[] += 1; kmin[] = min(kmin[], length(chain))
            else
                foreach(dfs, ps)
            end
        end
        pop!(chain)
    end
    for t in alive_at(g, top)
        dfs(t)
    end
    leaves[] > CAP && bump(Symbol(pre, "_cap"))
    bump(Symbol(pre, "_chains"), leaves[])
    bump(Symbol(pre, "_dead"), deads[])
    deads[] > 0 && bump(Symbol(pre, "_dead_states"))
    kmin[] < typemax(Int) && (C[Symbol(pre, "_kmin")] = min(get(C, Symbol(pre, "_kmin"), typemax(Int)), kmin[]))
end

# Tras el filtro de requisitos del UP (antes de la fila nueva): el pin que falta en Lean (LiveUp.lean).
Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        $(judge)(gpath, "flt")
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

function reviewed(g)
    h = deepcopy(g)
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    groups = ("flt", "arr", "join", "jrev", "fin")
    fields = ("states", "chains", "dead", "dead_states", "kmin", "cap")
    cols = [Symbol(g, "_", f) for g in groups for f in fields]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = MODE
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            Probes.with(:up_done => g -> judge(g, "arr"),
                        :join_post => g -> (judge(g, "join"); judge(reviewed(g), "jrev"))) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
            if SatMachine.have_solution(machine)
                for g in SatMachine.get_gpath_solutions(machine)
                    judge(reviewed(g), "fin")
                end
            end
        end
        PG.FORBID[] = :off
        val(c) = (v = get(C, c, 0); v == typemax(Int) ? "-" : (endswith(string(c), "kmin") && v == 0 ? "-" : v))
        return (truth, (val(c) for c in cols)..., round(t, digits = 1))
    end
end

main()
