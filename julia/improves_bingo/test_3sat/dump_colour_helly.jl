# Volcado de un estado con un trío sin testigo común en su color (29-sept-2026; sigue a probe_colour_helly.jl).
#
#   PROBE_MAP=bin julia --project=. test_3sat/dump_colour_helly.jl <cnf> [max_estados]
#
# En cada join, para P = [] y cada P de un nodo del mapa de un paso con elección, h = pin(unión, P) válido: busca
# triángulos (y, w, z) de h cuyos testigos del color c en el paso del remitente se cortan dos a dos pero no los tres.
# Del estado más pequeño (menos vivos) vuelca: el trío y sus testigos; qué deja la limpieza al fijar c y al fijar el
# otro color (vivos, aristas, qué nodos y aristas del trío sobreviven), y las camarillas llevadas por el trío en h.

const CNF = abspath(ARGS[1])
const MAXS = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 1
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
key(x) = Alias.as_key(x)
nk(n :: NodeId) = "($(n.step),$(n.index))"
choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)
pin(g, P) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(P)); g2)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
edges(h) = Set(keys(h.og.edges))

const FOUND = Any[]

function wit(og, k, c, y)
    [r for r in get(og.alive, k, SetPathNodesId()) if r.id == c && PG.has_edge(og, y, r)]
end

function scan(h, k, cols, P)
    og = h.og
    V = collect(alive(h))
    for c in cols
        W = Dict(y => Set(wit(og, k, c, y)) for y in V)
        for (i, y) in enumerate(V), j in i+1:length(V), l in j+1:length(V)
            w = V[j]; z = V[l]
            (PG.has_edge(og, y, w) && PG.has_edge(og, w, z) && PG.has_edge(og, y, z)) || continue
            (isempty(W[y] ∩ W[w]) || isempty(W[w] ∩ W[z]) || isempty(W[y] ∩ W[z])) && continue
            isempty(W[y] ∩ W[w] ∩ W[z]) || continue
            push!(FOUND, (h = deepcopy(h), k = k, c = c, other = first(filter(!=(c), cols)), P = P,
                          tri = (y, w, z), W = (W[y], W[w], W[z])))
            return
        end
    end
end

function on_join_post(u)
    k = u.current_step - 2
    k >= 0 || return
    cols = map_nodes(u.og, k)
    length(cols) == 2 || return
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    for kk in choice_steps(u.og), b in map_nodes(u.og, kk)
        push!(Ps, [b])
    end
    for P in Ps
        h = pin(u, P)
        h.is_valid && scan(h, k, cols, P)
    end
end

"¿Alguna camarilla llevada (cadena raíz → cima, poseída dos a dos) contiene los tres nodos? Y cuántas cadenas hay."
function tri_on_clique(h, tri; cap = 200000)
    og = h.og; top = h.current_step - 1
    chain = PathNodeId[]; n = Ref(0); hit = Ref(false)
    function ext(x)
        (hit[] || n[] > cap) && return
        push!(chain, x)
        if x.id.step == top
            n[] += 1
            all(t -> t in chain, tri) && (hit[] = true)
        else
            nd = PathCollectionLines.get_node(h.table_lines, x)
            if nd !== nothing
                for s in nd.sons
                    PG.is_alive(og, s) || continue
                    PathCollectionLines.get_node(h.table_lines, s) === nothing && continue
                    all(a -> PG.has_edge(og, a, s), chain) && ext(s)
                end
            end
        end
        pop!(chain)
    end
    for r in get(og.alive, 0, SetPathNodesId())
        r.parent_id === nothing || continue
        PathCollectionLines.get_node(h.table_lines, r) === nothing && continue
        ext(r)
    end
    return hit[], n[]
end

function describe(f)
    h = f.h; og = h.og
    println("== estado: paso actual $(h.current_step), paso del remitente k = $(f.k), P = [$(join(nk.(f.P), ", "))]")
    println("   vivos $(length(alive(h))), aristas $(length(edges(h))); color del trío c = $(nk(f.c)), otro = $(nk(f.other))")
    for c in (f.c, f.other)
        K = [r for r in get(og.alive, f.k, SetPathNodesId()) if r.id == c]
        println("   clase $(nk(c)) en k: ", join(key.(K), "  "))
    end
    on, nch = tri_on_clique(h, f.tri)
    println("   camarillas (cadenas completas) en h: $(nch); alguna contiene el trío: $(on)")
    println("-- trío (se poseen dos a dos):")
    for (y, W) in zip(f.tri, f.W)
        println("   ", key(y), "   testigos de $(nk(f.c)): {", join(key.(collect(W)), ", "), "}")
    end
    for c in (f.c, f.other)
        g = pin(h, [c])
        println("-- fijar $(nk(c)): válido = $(g.is_valid)")
        g.is_valid || continue
        A = alive(g); E = edges(g)
        println("   vivos $(length(A)) de $(length(alive(h))), aristas $(length(E)) de $(length(edges(h)))")
        println("   del trío siguen vivos: ", join([key(y) for y in f.tri if y in A], ", "))
        (y, w, z) = f.tri
        for (p, q) in ((y, w), (w, z), (y, z))
            println("   arista ", key(p), " — ", key(q), ": ", PG.has_edge(g.og, p, q) ? "sigue" : "cortada")
        end
        K = [r for r in get(g.og.alive, f.k, SetPathNodesId())]
        println("   vivos en k tras fijar: ", join(key.(K), "  "))
        # por paso: cuántos vivos quedan
        println("   vivos por paso: ", join(["$(s):$(length(get(g.og.alive, s, SetPathNodesId())))" for s in 0:h.current_step-1], " "))
    end
    println("-- vivos por paso en h: ", join(["$(s):$(length(get(og.alive, s, SetPathNodesId())))" for s in 0:h.current_step-1], " "))
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    machine = SatMachine.new(loader(CNF))
    Probes.with(:join_post => on_join_post) do
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
    end
    println("estados con trío fallido: $(length(FOUND))")
    both = count(f -> length(map_nodes(f.h.og, f.k)) == 2, FOUND)
    println("   con los dos colores vivos en k: $(both); con un solo color: $(length(FOUND) - both)")
    ondead = count(f -> !tri_on_clique(f.h, f.tri)[1], FOUND)
    println("   trío fuera de toda camarilla: $(ondead) de $(length(FOUND))")
    isempty(FOUND) && return
    sort!(FOUND, by = f -> (length(map_nodes(f.h.og, f.k)) == 2 ? 0 : 1, length(alive(f.h))))
    for f in FOUND[1:min(MAXS, end)]
        describe(f)
    end
end

main()
