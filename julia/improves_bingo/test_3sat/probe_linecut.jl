# ¿De dónde viene el corte cruzado? La historia de las bases por las líneas (1-oct-2026, rama reader-stuck).
#
#   PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_linecut.jl <salida.tsv>
#
# Con FORBID = :on. Las entradas de cada línea son los remitentes de los envíos (una por clave y paso).
#
# A — LineCut: para cada línea con dos entradas a y b, y cada triángulo prohibido en a (con sus tres aristas):
#   lc_dead, lc_open (b lo tiene como triángulo sin prohibir: los dos no coinciden).
#   Por categorías, según la mejor cima de a vecina de los tres nodos (ninguna: «nostar»; o el número de caras con esa
#   cima sin prohibir, 0–3): columna cats con «E:cat=prohibidos/abiertos» para las entradas de una línea y «A:…» para
#   las dos llegadas de un join.
# B — la historia de las bases «TopFace» de las llegadas de cada join (cima t de la llegada S, base prohibida en S,
#   t vecina de los tres con sus tres caras sin prohibir): con m el paso más alto de la base y T la línea de los
#   remitentes, se mira la base en todas las entradas de las líneas m+1 … T:
#   bases
#   born_cut   — cortada en todas las entradas de todas esas líneas (desde que existe su nodo más alto)
#   late       — alguna entrada de alguna línea la tiene abierta; first_all = la primera línea desde la que todas
#                las entradas la cortan, contada desde m+1 (histograma «d=n»)
#   en la línea m+1, en la entrada que tiene el nodo más alto como cima: born_edge (falta una arista), born_dead
#   (prohibida), born_open (abierta)

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
nodes(g, b) = all(n -> PG.is_alive(g.og, n), b)
cut(g, b) = !tri(g, b) || PG.dead_trio(g.og, b[1], b[2], b[3])

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
    out = NTuple{3, PathNodeId}[]
    for b in dead_tris(S)
        any(x -> st(x) == top, b) && continue
        for t in tops
            all(x -> edge(S, t, x), b) || continue
            (PG.dead_trio(S.og, t, b[1], b[2]) || PG.dead_trio(S.og, t, b[1], b[3]) || PG.dead_trio(S.og, t, b[2], b[3])) && continue
            push!(out, b); break
        end
    end
    return out
end

# la mejor cima de g para el triángulo b: "nostar", o el máximo de caras sin prohibir (0..3)
function cat(g, b)
    top = Int(g.current_step) - 1
    any(x -> st(x) == top, b) && return "hastop"
    best = -1
    for t in alive_at(g, top)
        all(x -> edge(g, t, x), b) || continue
        k = count(!, (PG.dead_trio(g.og, t, b[1], b[2]), PG.dead_trio(g.og, t, b[1], b[3]), PG.dead_trio(g.og, t, b[2], b[3])))
        best = max(best, k)
    end
    return best < 0 ? "nostar" : "f$best"
end
function cats(tag, a, b)
    for q in dead_tris(a)
        c = cat(a, q)
        bump("$tag:$c:dead")
        cut(b, q) || bump("$tag:$c:open")
    end
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
    header = "instance\ttruth\tlc_dead\tlc_open\tbases\tborn_cut\tlate\tborn_edge\tborn_dead\tborn_open\tfirst_all\tcats\tsecs"
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
            # A — LineCut
            for (L, es) in lines
                gs = collect(values(es))
                length(gs) == 2 || continue
                for (a, b) in ((gs[1], gs[2]), (gs[2], gs[1]))
                    cats("E", a, b)
                    for q in dead_tris(a)
                        bump("lc_dead")
                        cut(b, q) || bump("lc_open")
                    end
                end
            end
            # B — la historia de las bases TopFace
            groups = Dict{Any, Vector{Any}}()
            for s in SENDS
                push!(get!(groups, (s[3], Int(s[1].current_step)), Any[]), s)
            end
            for ((d, T), ss) in groups
                length(ss) == 2 || continue
                A1, A2 = arrival(ss[1]), arrival(ss[2])
                (A1.is_valid && A2.is_valid) || continue
                cats("A", A1, A2); cats("A", A2, A1)
                for S in (A1, A2), b in topface(S)
                    bump("bases")
                    m = maximum(st, b)
                    hi = b[argmax(map(st, b))]
                    firstall = m + 1; allcut = true
                    for L in (m + 1):T
                        es = collect(values(get(lines, L, Dict{Any, Any}())))
                        if !all(g -> cut(g, b), es)
                            allcut = false; firstall = L + 1
                        end
                    end
                    allcut ? bump("born_cut") : (bump("late"); bump("d=$(firstall - (m + 1))"))
                    bump("s=$(T - firstall)")     # líneas, antes de la de los remitentes, desde las que todas cortan
                    for g in values(get(lines, m + 1, Dict{Any, Any}()))
                        PG.is_alive(g.og, hi) || continue
                        !tri(g, b) ? bump("born_edge") : (PG.dead_trio(g.og, b[1], b[2], b[3]) ? bump("born_dead") : bump("born_open"))
                    end
                end
            end
        end
        PG.FORBID[] = :off
        hist = join(sort(["$k:$v" for (k, v) in C if startswith(k, "d=")]), " ") * " || " *
               join(sort(["$k:$v" for (k, v) in C if startswith(k, "s=")], by = x -> parse(Int, split(split(x, ":")[1], "=")[2])), " ")
        cs = String[]
        for tag in ("E", "A"), c in ("hastop", "nostar", "f0", "f1", "f2", "f3")
            d = get(C, "$tag:$c:dead", 0)
            d > 0 && push!(cs, "$tag:$c=$d/$(get(C, "$tag:$c:open", 0))")
        end
        return (truth, (get(C, k, 0) for k in ("lc_dead", "lc_open", "bases", "born_cut", "late", "born_edge", "born_dead", "born_open"))..., hist, join(cs, " "), round(t, digits = 1))
    end
end

main()
