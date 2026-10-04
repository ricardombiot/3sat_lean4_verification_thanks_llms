# El corte cruzado por dentro (1-oct-2026, rama reader-stuck; lean ForbidOnStar.lean, CrossCut).
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_crosscut.jl <salida.tsv>
#
# Con FORBID = :on. Se guardan los envíos de la máquina (remitente g antes del filtro, requisitos, destino) y, para
# cada destino con dos llegadas válidas S y O (un join), con Y = filtro(g) y la llegada = up(Y), se clasifican los
# tetraedros «TopFace» de S (base (x, y, z) prohibida en S con sus tres aristas, cima t de S vecina de los tres con sus
# tres caras sin prohibir):
#   nivel   — hi: la base toca el paso del remitente (cima - 1); lo: toda ella dos pasos o más por debajo de la cima
#   en S    — dónde murió la base: sender (ya prohibida en el remitente), filter (la prohíbe la regla en el review del
#             filtro), up (la prohíbe la regla en el review de la llegada)
#   en O    — por qué la corta el otro lado, y dónde: node/edge/dead × sender/filter/up; open si no la corta
# La fila de cada instancia lleva «nivel|S|O=cuenta» ordenado por cuenta, y:
#   y «P:patrón=cuenta»: las caras (12, 13, 23) de la base con cada padre de la cima, en el remitente de S
#   (o = sin prohibir, D = prohibida, - = falta una arista), los padres ordenados;
#   tetra, open, both_senders (la base ya está cortada en los dos remitentes), same_sender (los dos remitentes ya
#   la tienen prohibida, con sus tres aristas)

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{String, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const SENDS = Any[]

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.is_valid && push!($(SENDS), (deepcopy(gpath), copy(requires), map_id_node, title, prohibited))
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
edge(g, a, b) = PG.has_edge(g.og, a, b)
st(x) = Int(x.id.step)
tri(g, b) = edge(g, b[1], b[2]) && edge(g, b[1], b[3]) && edge(g, b[2], b[3])
deadb(g, b) = tri(g, b) && PG.dead_trio(g.og, b[1], b[2], b[3])
nodes(g, b) = all(n -> PG.is_alive(g.og, n), b)
cut(g, b) = !tri(g, b) || PG.dead_trio(g.og, b[1], b[2], b[3])

function topface(S)
    top = Int(S.current_step) - 1
    tops = alive_at(S, top)
    out = NTuple{4, PathNodeId}[]
    for (k, e) in S.og.edges, r in collect(e.forbid)
        (edge(S, e.a, r) && edge(S, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        any(x -> st(x) == top, (e.a, e.b, r)) && continue
        for t in tops
            all(x -> edge(S, t, x), (e.a, e.b, r)) || continue
            (PG.dead_trio(S.og, t, e.a, e.b) || PG.dead_trio(S.og, t, e.a, r) || PG.dead_trio(S.og, t, e.b, r)) && continue
            push!(out, (t, e.a, e.b, r))
            break
        end
    end
    return out
end

function stages(send)
    (g0, reqs, d, title, proh) = send
    Y = deepcopy(g0)
    GraphPath.filter!(Y, reqs)
    A = deepcopy(Y)
    Y.is_valid && GraphPath.do_up!(A, d, title, proh)
    return (g0, Y, A)
end

where3(f, g0, Y) = f(g0) ? "sender" : (f(Y) ? "filter" : "up")

function judge(SS, OO)
    (gS, YS, S) = SS; (gO, YO, O) = OO
    top = Int(S.current_step) - 1
    for q in topface(S)
        b = (q[2], q[3], q[4])
        bump("tetra")
        lvl = all(n -> st(n) <= top - 2, b) ? "lo" : "hi"
        sS = where3(g -> deadb(g, b), gS, YS)
        sO = if !nodes(O, b)
            "node:" * where3(g -> !nodes(g, b), gO, YO)
        elseif !tri(O, b)
            "edge:" * where3(g -> nodes(g, b) && !tri(g, b), gO, YO)
        elseif PG.dead_trio(O.og, b[1], b[2], b[3])
            "dead:" * where3(g -> deadb(g, b), gO, YO)
        else
            bump("open"); "open"
        end
        bump("$lvl|$sS|$sO")
        nd = PathCollectionLines.get_node(S.table_lines, q[1])
        bs = sort(collect(b), by = st)
        pats = String[]
        for p in nd.parents
            PG.is_alive(S.og, p) || continue
            push!(pats, join([(edge(gS, p, bs[i]) && edge(gS, p, bs[j])) ? (PG.dead_trio(gS.og, p, bs[i], bs[j]) ? "D" : "o") : "-"
                              for (i, j) in ((1, 2), (1, 3), (2, 3))]))
        end
        bump("P:" * join(sort(pats), "+"))
        (cut(gS, b) && cut(gO, b)) && bump("both_senders")
        (deadb(gS, b) && deadb(gO, b)) && bump("same_sender")
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    header = "instance\ttruth\tjoins\ttetra\topen\tboth_senders\tsame_sender\tclases\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SENDS)
        PG.FORBID[] = :on
        joins = 0
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            groups = Dict{Any, Vector{Any}}()
            for s in SENDS
                push!(get!(groups, (s[3], Int(s[1].current_step)), Any[]), s)
            end
            for (_, ss) in groups
                length(ss) == 2 || continue
                X1, X2 = stages(ss[1]), stages(ss[2])
                (X1[3].is_valid && X2[3].is_valid) || continue
                joins += 1
                judge(X1, X2); judge(X2, X1)
            end
        end
        PG.FORBID[] = :off
        main_keys = ("tetra", "open", "both_senders", "same_sender")
        classes = sort([(v, k) for (k, v) in C if !(k in main_keys)], rev = true)
        return (truth, joins, (get(C, k, 0) for k in main_keys)..., join(["$k=$v" for (v, k) in classes], " "), round(t, digits = 1))
    end
end

main()
