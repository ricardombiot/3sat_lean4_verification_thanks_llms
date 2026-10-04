# El residuo de PrevCut tras descontar la herencia (1-oct-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_prevnew.jl <salida.tsv>
#
# Con FORBID = :on. Mide `HPrevNew` (lean ForbidOnInherit.lean) sobre TODAS las llegadas válidas. Para cada base baja
# de `PrevCut` (base prohibida en la llegada S de la entrada `a` de la línea T, bajo una cima de S con sus tres caras
# sin prohibir, con sus nodos por debajo del paso T-1), se mira la base en `a` (antes del filtro y del UP):
#
#   inherit — `a` ya la tenía muerta bajo una cima suya con tres caras vivas (`DeadBase a`) y sus nodos están por
#             debajo del paso T-2: la cierra la inducción (`prevCut_inherit`); no entra en `HPrevNew`
#   salv    — `DeadBase a`, pero la base tiene un nodo en el paso T-2 (la cima de la línea anterior)
#   birth   — prohibida en `a`, y ninguna cima de `a` sostiene las tres caras
#   c_open  — en `a` es un triángulo sin prohibir (la prohíbe el review del filtro o del UP)
#   c_edge  — a `a` le falta una arista (no debería pasar: la llegada no gana aristas viejas)
#   res_open / inh_open — de las del residuo (salv + birth + c_*) / de las heredadas, las que alguna entrada de la
#             línea T-1 no corta (se espera 0)
#   inh_notpar — heredadas en que ninguna cima de `a` que sostiene las tres caras es padre de la cima de la llegada
#   fp_faces / fp_fail — `arrOn_face_parent`: caras (cima de la llegada, dos nodos de la base) y las que no tienen
#             un padre de la cima que las sostenga en `a` (demostrado: se espera 0; comprueba el espejo Lean–Julia)
#   birth_k — en las de nacimiento, cuántos padres distintos hacen falta como mínimo para sostener las tres caras

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
compat(p, t) = t.parent_id == p.id && t.gparent_id == p.parent_id
const FACES = ((1, 2), (1, 3), (2, 3))

# la cima `p` de `g` sostiene la cara `(u, w)`: vecina de los dos, y el trío sin prohibir
holds(g, p, u, w) = edge(g, p, u) && edge(g, p, w) && edge(g, u, w) && !PG.dead_trio(g.og, p, u, w)
holds3(g, p, b) = all(f -> holds(g, p, b[f[1]], b[f[2]]), FACES)

function dead_tris(g)
    out = NTuple{3, PathNodeId}[]
    for (k, e) in g.og.edges, r in collect(e.forbid)
        (edge(g, e.a, r) && edge(g, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        push!(out, (e.a, e.b, r))
    end
    return out
end

# las bases de `PrevCut` de la llegada S, cada una con las cimas de S que tienen sus tres caras sin prohibir
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

# el mínimo de padres de `t` (cimas de `a`) que hacen falta para sostener las tres caras de `b`; 9 si alguna no se sostiene
function min_parents(a, ps, b)
    hs = [Set(p for p in ps if holds(a, p, b[f[1]], b[f[2]])) for f in FACES]
    any(isempty, hs) && return 9
    isempty(intersect(hs...)) || return 1
    for p in ps, q in ps
        all(h -> p in h || q in h, hs) && return 2
    end
    return 3
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    keys = ("pc_bases", "inherit", "salv", "birth", "c_open", "c_edge", "res_open", "inh_open", "inh_notpar",
            "fp_faces", "fp_fail")
    header = "instance\ttruth\t" * join(keys, "\t") * "\tbirth_k\tsecs"
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
            # las entradas de cada línea
            lines = Dict{Int, Dict{Any, Any}}()
            for s in SENDS
                get!(get!(lines, Int(s[1].current_step), Dict{Any, Any}()), s[1].map_parent_id, s[1])
            end
            for s in SENDS
                a = s[1]
                T = Int(a.current_step)
                A = arrival(s)
                A.is_valid || continue
                atops = alive_at(a, T - 1)
                prev = values(get(lines, T - 1, Dict{Any, Any}()))
                for (b, ts) in topface(A)
                    maximum(st, b) >= T - 1 && continue
                    bump("pc_bases")
                    open = !all(g -> cut(g, b), prev)
                    # `arrOn_face_parent`: cada cara de cada cima la sostiene un padre en `a`
                    for tt in ts, f in FACES
                        bump("fp_faces")
                        any(p -> compat(p, tt) && holds(a, p, b[f[1]], b[f[2]]), atops) || bump("fp_fail")
                    end
                    if !tri(a, b)
                        bump("c_edge"); open && bump("res_open")
                    elseif !PG.dead_trio(a.og, b[1], b[2], b[3])
                        bump("c_open"); open && bump("res_open")
                    else
                        hs = [p for p in atops if holds3(a, p, b)]
                        if isempty(hs)
                            bump("birth"); open && bump("res_open")
                            k = minimum(min_parents(a, [p for p in atops if compat(p, tt)], b) for tt in ts)
                            bump("k=$k")
                        elseif maximum(st, b) >= T - 2
                            bump("salv"); open && bump("res_open")
                        else
                            bump("inherit"); open && bump("inh_open")
                            any(p -> any(tt -> compat(p, tt), ts), hs) || bump("inh_notpar")
                        end
                    end
                end
            end
        end
        PG.FORBID[] = :off
        hist = join(sort(["$k:$v" for (k, v) in C if startswith(k, "k=")]), " ")
        return (truth, (get(C, k, 0) for k in keys)..., hist, round(t, digits = 1))
    end
end

main()
