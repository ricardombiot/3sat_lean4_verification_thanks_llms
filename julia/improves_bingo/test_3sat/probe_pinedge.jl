# PinEdgeMono (30-sept-2026, rama reader-stuck; tras probe_crossline).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_pinedge.jl <salida.tsv>
#
# Las llegadas de un mismo remitente a los dos destinos de un paso (fijadas a valores opuestos del literal, en los
# pasos de cláusula): para cada pareja de nodos por debajo de la cima vivos en las dos, ¿son vecinos en una y no en
# la otra? Y respecto al remitente sin fijar (copia antes del filtro): ¿el pin quitó una arista entre dos nodos que
# sobreviven?
#   pairs_both, diff (vecinos en una llegada y no en la otra), diff_far (con los dos nodos a más de 2 pasos por encima
#   del literal), cut_by_pin (arista del remitente entre supervivientes que la llegada no tiene), cut_far

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const SENDS = Any[]

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        pre = deepcopy(gpath)
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
        gpath.is_valid && push!($(SENDS), (pre, deepcopy(gpath), copy(requires)))
    end
end)

allalive(g) = [x for (_, xs) in g.og.alive for x in xs]

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:arrivals, :pairs_both, :diff, :diff_far, :cut_by_pin, :cut_far)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDS)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            C[:arrivals] = length(SENDS)
            # agrupar por remitente (mismo estado de partida: misma clave y paso)
            groups = Dict{Any, Vector{Any}}()
            for (pre, arr, req) in SENDS
                push!(get!(groups, (pre.map_parent_id, Int(pre.current_step)), Any[]), (pre, arr, req))
            end
            for (_, grp) in groups
                # el pin quita aristas entre supervivientes
                for (pre, arr, req) in grp
                    lit = isempty(req) ? -100 : Int(first(req).step)
                    xs = [x for x in allalive(arr) if Int(x.id.step) < Int(pre.current_step)]
                    for i in eachindex(xs), j in i+1:length(xs)
                        a, b = xs[i], xs[j]
                        PG.has_edge(pre.og, a, b) && !PG.has_edge(arr.og, a, b) || continue
                        bump(:cut_by_pin)
                        min(Int(a.id.step), Int(b.id.step)) > lit + 2 && bump(:cut_far)
                    end
                end
                length(grp) == 2 || continue
                (p1, a1, r1), (p2, a2, r2) = grp
                lit = isempty(r1) ? -100 : Int(first(r1).step)
                top = Int(p1.current_step)
                xs = [x for x in allalive(a1) if Int(x.id.step) < top && PG.is_alive(a2.og, x)]
                for i in eachindex(xs), j in i+1:length(xs)
                    a, b = xs[i], xs[j]
                    bump(:pairs_both)
                    if PG.has_edge(a1.og, a, b) != PG.has_edge(a2.og, a, b)
                        bump(:diff)
                        min(Int(a.id.step), Int(b.id.step)) > lit + 2 && bump(:diff_far)
                    end
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
