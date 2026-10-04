# El nacimiento de PrevCut por dentro (1-oct-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_birth.jl <salida.tsv>
#
# Con FORBID = :on, sobre TODAS las llegadas válidas. Una base de **nacimiento** (lean ForbidOnInherit.lean, el residuo
# de `HPrevNew`): base baja `B`, prohibida en la llegada S de la entrada `a` (línea T, clave k) bajo una cima `t` con
# sus tres caras sin prohibir, prohibida ya en `a`, y sin ninguna cima de `a` que sostenga las tres caras. Los padres
# de `t` son cimas `(k, c, g)` de `a`: mismo color `c` del paso T-2, distinto color `g` del paso T-3.
#
#   births
#   pat      — el patrón de los dos padres, cara a cara (12, 13, 23): o sostiene, D aristas con el trío prohibido,
#              - falta una arista
#   shape    — `a` es una sola llegada (single) o la unión de dos (join); y cómo corta la base cada llegada que la
#              forma: la del color c («Sc») y la otra («So»): node (falta un nodo), edge (falta una arista), dead
#              (prohibida), open
#   prev     — cómo corta la base cada entrada de la línea T-1: la de clave c («ec») y la otra («eo»)
#   since    — cuántas líneas antes de la T-1 la cortan ya todas las entradas (0: la T-1 es la primera)
#   En el patrón «un padre lleno con una cara D (u, w) y tercer nodo v; el otro padre sostiene (u, w) y no es vecino
#   de v», con gf, gh los colores del paso T-3 de cada padre, en la línea T-2:
#   l2       — cómo corta la base la entrada de clave gf («Ef») y la de clave gh («Eh»); «hi» si la base tiene un nodo
#              en el paso T-2 (no existe aún en esa línea)
#   l2v      — en Eh: v vivo o no («v+», «v-»);  l2uw — en Ef: la arista u–w está o no («uw+», «uw-»)
#   back     — las dos llegadas de la línea T-2 al color c (los lados de la entrada «ec»), por el color de su
#              remitente (f, h): «cómo corta la base el remitente > cómo la corta su llegada»; hi/lo según la base
#              tenga o no un nodo en el paso T-2

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
cut(g, b) = !tri(g, b) || PG.dead_trio(g.og, b[1], b[2], b[3])
how(g, b) = !all(n -> PG.is_alive(g.og, n), b) ? "node" : !tri(g, b) ? "edge" :
            PG.dead_trio(g.og, b[1], b[2], b[3]) ? "dead" : "open"
compat(p, t) = t.parent_id == p.id && t.gparent_id == p.parent_id
const FACES = ((1, 2), (1, 3), (2, 3))
holds(g, p, u, w) = edge(g, p, u) && edge(g, p, w) && edge(g, u, w) && !PG.dead_trio(g.og, p, u, w)
holds3(g, p, b) = all(f -> holds(g, p, b[f[1]], b[f[2]]), FACES)
face(g, p, u, w) = !(edge(g, p, u) && edge(g, p, w)) ? '-' : PG.dead_trio(g.og, p, u, w) ? 'D' : 'o'
sig(g, p, b) = String([face(g, p, b[f[1]], b[f[2]]) for f in FACES])

function dead_tris(g)
    out = NTuple{3, PathNodeId}[]
    for (k, e) in g.og.edges, r in collect(e.forbid)
        (edge(g, e.a, r) && edge(g, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        push!(out, (e.a, e.b, r))
    end
    return out
end

function topface(S)
    top = Int(S.current_step) - 1
    tops = alive_at(S, top)
    out = Tuple{NTuple{3, PathNodeId}, Vector{PathNodeId}}[]
    for b in dead_tris(S)
        any(x -> st(x) == top, b) && continue
        ts = [t for t in tops if all(x -> edge(S, t, x), b) && holds3(S, t, b)]
        isempty(ts) || push!(out, (b, ts))
    end
    return out
end

function arrival(send)
    (g0, reqs, d, title, proh) = send
    A = deepcopy(g0)
    GraphPath.filter!(A, reqs)
    A.is_valid && GraphPath.do_up!(A, d, title, proh)
    return A
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    header = "instance\ttruth\tbirths\tpat\tshape\tprev\tsince\tl2\tl2v\tl2uw\tback\tsecs"
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
            lines = Dict{Int, Dict{Any, Any}}()
            for s in SENDS
                get!(get!(lines, Int(s[1].current_step), Dict{Any, Any}()), s[1].map_parent_id, s[1])
            end
            # los envíos por (línea del remitente, destino)
            into = Dict{Any, Vector{Any}}()
            for s in SENDS
                push!(get!(into, (Int(s[1].current_step), s[3]), Any[]), s)
            end
            arrs = Dict{Any, Any}()
            for s in SENDS
                a = s[1]
                T = Int(a.current_step)
                k = a.map_parent_id
                A = arrival(s)
                A.is_valid || continue
                atops = alive_at(a, T - 1)
                prev = get(lines, T - 1, Dict{Any, Any}())
                bases = [(b, ts) for (b, ts) in topface(A) if maximum(st, b) < T - 1 && tri(a, b) &&
                         PG.dead_trio(a.og, b[1], b[2], b[3]) && !any(p -> holds3(a, p, b), atops)]
                isempty(bases) && continue
                # las llegadas que forman `a`, por la clave de su remitente
                sides = Dict{Any, Any}()
                for s2 in get(into, (T - 1, k), Any[])
                    S2 = arrival(s2)
                    S2.is_valid && (sides[s2[1].map_parent_id] = S2)
                end
                for (b, ts) in bases
                    bump("births")
                    tt = ts[1]
                    ps = [p for p in atops if compat(p, tt)]
                    bump("pat:" * join(sort([sig(a, p, b) for p in ps]), "/"))
                    c = tt.gparent_id
                    # la forma de `a`
                    tag = length(sides) == 2 ? "join" : length(sides) == 1 ? "single" : "n$(length(sides))"
                    for (key, S2) in sides
                        bump("shape:$tag:" * (key == c ? "Sc" : "So") * "=" * how(S2, b))
                    end
                    # la línea anterior
                    for (key, e) in prev
                        bump("prev:" * (key == c ? "ec" : "eo") * "=" * how(e, b))
                    end
                    length(prev) == 1 && bump("prev:eo=none")
                    # desde cuándo la cortan todas
                    m = maximum(st, b)
                    firstall = m + 1
                    for L in (m + 1):(T - 1)
                        all(g -> cut(g, b), values(get(lines, L, Dict{Any, Any}()))) || (firstall = L + 1)
                    end
                    bump("since:$(T - 1 - firstall)")
                    # el patrón de dos colores, en la línea T-2
                    length(ps) == 2 || continue
                    full = [p for p in ps if all(x -> edge(a, p, x), b)]
                    length(full) == 1 || (bump("l2:nofull"); continue)
                    pf = full[1]; ph = ps[1] == pf ? ps[2] : ps[1]
                    ds = [f for f in FACES if face(a, pf, b[f[1]], b[f[2]]) == 'D']
                    length(ds) == 1 || (bump("l2:D$(length(ds))"); continue)
                    f = ds[1]; u, w = b[f[1]], b[f[2]]; v = b[6 - f[1] - f[2]]
                    # las llegadas de la línea T-2 al color c (los dos lados de la entrada `ec`)
                    for s3 in get(into, (T - 2, c), Any[])
                        g = s3[1].map_parent_id
                        g == pf.gparent_id || g == ph.gparent_id || continue
                        S3 = get!(() -> arrival(s3), arrs, (T - 2, g, c))
                        S3.is_valid || continue
                        side = g == pf.gparent_id ? "f" : "h"
                        bump("back:$(m >= T - 2 ? "hi" : "lo"):$side:" * how(s3[1], b) * ">" * how(S3, b))
                    end
                    if m >= T - 2
                        bump("l2:hi"); continue
                    end
                    l2 = get(lines, T - 2, Dict{Any, Any}())
                    Ef = get(l2, pf.gparent_id, nothing); Eh = get(l2, ph.gparent_id, nothing)
                    bump("l2:Ef=" * (Ef === nothing ? "none" : how(Ef, b)))
                    bump("l2:Eh=" * (Eh === nothing ? "none" : how(Eh, b)))
                    Eh === nothing || bump(PG.is_alive(Eh.og, v) ? "l2v:v+" : "l2v:v-")
                    Ef === nothing || bump(edge(Ef, u, w) ? "l2uw:uw+" : "l2uw:uw-")
                end
            end
        end
        PG.FORBID[] = :off
        col(pre) = join(sort(["$(k[length(pre)+1:end]):$v" for (k, v) in C if startswith(k, pre)]), " ")
        return (truth, get(C, "births", 0), col("pat:"), col("shape:"), col("prev:"), col("since:"), col("l2:"),
                col("l2v:"), col("l2uw:"), col("back:"), round(t, digits = 1))
    end
end

main()
