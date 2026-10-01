# PrevCut y CrossCut en instancias mayores, con ventana de dos líneas (1-oct-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_prevbig.jl <salida.tsv>
#
# Con FORBID = :on. Mismas medidas que probe_prevnew.jl / probe_crosscut.jl / probe_norule.jl, pero sin guardar todos
# los envíos: se procesan línea a línea según llegan y solo se retienen los de la línea en curso y la anterior, para
# que quepan v7 y v8 en el tope de memoria.
#
# Para cada llegada válida S = arrOn a d (a en la línea T) y cada base muerta de S (triángulo prohibido en S bajo una
# cima de S con sus tres caras sin prohibir):
#
#   pc_bases / pc_open  PrevCut: bases con sus nodos por debajo del paso T-1 / alguna entrada de la línea T-1 no la corta
#   c_open              la base es en `a` un triángulo sin prohibir (la prohíbe la regla del review en la llegada)
#   pc_hi               bases con un nodo en la cima de `a` (no entran en PrevCut)
#   cc_bases / cc_open  CrossCut: bases de las llegadas que entran en un join / la otra llegada no la corta
#   cs_open             … la entrada que envía la otra llegada no la corta
#   rule_new, cats      triángulos viejos de S que en `a` están sin prohibir, por zona y categoría (probe_norule.jl)
#   ooo                 envíos fuera de orden de línea (se espera 0; si no, la ventana no vale)

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{String, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const BUF = Dict{Int, Vector{Any}}()
const CUR = Ref(-1)

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
edge(g, a, b) = PG.has_edge(g.og, a, b)
st(x) = Int(x.id.step)
tri(g, b) = edge(g, b[1], b[2]) && edge(g, b[1], b[3]) && edge(g, b[2], b[3])
cut(g, b) = !tri(g, b) || PG.dead_trio(g.og, b[1], b[2], b[3])
nfaces(g, t, b) = count(!, (PG.dead_trio(g.og, t, b[1], b[2]), PG.dead_trio(g.og, t, b[1], b[3]), PG.dead_trio(g.og, t, b[2], b[3])))

function dead_tris(g)
    out = NTuple{3, PathNodeId}[]
    for (k, e) in g.og.edges, r in collect(e.forbid)
        (edge(g, e.a, r) && edge(g, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        push!(out, (e.a, e.b, r))
    end
    return out
end

# la mejor cima de g para el triángulo b: -1 si ninguna es vecina de los tres, o el máximo de caras sin prohibir
function best(g, tops, b)
    k = -1
    for t in tops
        all(x -> edge(g, t, x), b) || continue
        k = max(k, nfaces(g, t, b))
    end
    return k
end

function arrival(send)
    (g0, reqs, d, title, proh) = send
    A = deepcopy(g0)
    GraphPath.filter!(A, reqs)
    A.is_valid && GraphPath.do_up!(A, d, title, proh)
    return A
end

# procesa la línea T con sus envíos y las entradas de la línea T-1
function process_line(T)
    sends = get(BUF, T, Any[])
    prev = Dict{Any, Any}()
    for s in get(BUF, T - 1, Any[])
        get!(prev, s[1].map_parent_id, s[1])
    end
    groups = Dict{Any, Vector{Any}}()
    for s in sends
        S = arrival(s)
        S.is_valid || continue
        push!(get!(groups, s[3], Any[]), (s[1], S))
    end
    for (d, arrs) in groups, (i, (a, S)) in enumerate(arrs)
        bump("arrivals")
        tops = alive_at(S, Int(S.current_step) - 1)
        other = length(arrs) == 2 ? arrs[3 - i] : nothing
        for b in dead_tris(S)
            m = maximum(st, b)
            m < T || continue                      # triángulo viejo
            k = best(S, tops, b)
            isopen = tri(a, b) && !PG.dead_trio(a.og, b[1], b[2], b[3])
            zone = m == T - 1 ? "top" : "low"
            cat = k < 0 ? "nostar" : "f$k"
            bump("$zone:$cat:dead")
            if isopen
                bump("rule_new"); bump("$zone:$cat:new")
            end
            k == 3 || continue                     # base muerta bajo una cima con tres caras vivas
            if other !== nothing
                bump("cc_bases")
                cut(other[2], b) || bump("cc_open")
                cut(other[1], b) || bump("cs_open")
            end
            if m >= T - 1
                bump("pc_hi")
            else
                bump("pc_bases")
                isopen && bump("c_open")
                all(g -> cut(g, b), values(prev)) || bump("pc_open")
            end
        end
    end
    delete!(BUF, T - 1)
end

function on_send(gpath, requires, map_id_node, title, prohibited)
    T = Int(gpath.current_step)
    if T < CUR[]
        bump("ooo")
    elseif T > CUR[]
        CUR[] >= 0 && process_line(CUR[])
        CUR[] = T
    end
    bump("sends")
    push!(get!(BUF, T, Any[]), (deepcopy(gpath), copy(requires), map_id_node, title, prohibited))
end

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.is_valid && $(on_send)(gpath, requires, map_id_node, title, prohibited)
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

function main()
    _, loader, _ = ProbeLib.map_of_env()
    keys = ("sends", "arrivals", "ooo", "pc_bases", "pc_open", "c_open", "pc_hi", "cc_bases", "cc_open", "cs_open",
            "rule_new")
    header = "instance\ttruth\t" * join(keys, "\t") * "\tcats\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(BUF); CUR[] = -1
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            CUR[] >= 0 && process_line(CUR[])
        end
        PG.FORBID[] = :off
        cs = String[]
        for zone in ("top", "low"), c in ("nostar", "f0", "f1", "f2", "f3")
            d = get(C, "$zone:$c:dead", 0)
            d > 0 && push!(cs, "$zone:$c=$d/$(get(C, "$zone:$c:new", 0))")
        end
        return (truth, (get(C, k, 0) for k in keys)..., join(cs, " "), round(t, digits = 1))
    end
end

main()
