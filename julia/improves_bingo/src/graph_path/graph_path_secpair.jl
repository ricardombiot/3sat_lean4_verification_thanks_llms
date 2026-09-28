# 28-sept-2026
#
# SecPair: el grafo de owners es la unión de sus secciones (espejo de
# lean/improves_bingo/AbsSatBingo/Model/SecPair.lean; escalera_reader §4.3).
#
# Una consulta, no una regla: la máquina no la usa. La sonda test_3sat/probe_tri_sec.jl la mete en el review
# (modos sec/secx) y mide que no corta nada.
#
# Sección de un grupo xs de vivos del paso k: la parte del grafo compatible con fijarlo. y está si algún x de
# xs lo posee; su tabla en la sección es ∪_x (inc[y] ∩ inc[x]). Después, el punto fijo de la regla de parejas
# dentro de la sección (con purga de nodos que se quedan sin entrada en algún paso). Es la mayor `R` de
# SecClosed (by = :map, xs = los vivos de un nodo del mapa) o de SecClosedX (by = :node, xs = un solo x).
#
# SecPair: en cada paso con elección (vivos de dos nodos del mapa distintos, Lean `choiceAt`), cada arista
# está en la sección de algún grupo. sec_pair_bad devuelve las aristas que no lo cumplen (vacío ⇔ SecPair).

const SecAdj = Dict{PathNodeId, Dict{Step, SetPathNodesId}}

function sec_section(og :: OwnersGraph, xs) :: SecAdj
    adj = SecAdj()
    #! [for] $ O(7*N*S*7) $
    for x in xs, y in PathOwnersGraph.neighbors_all(og, x)
        t = get!(adj, y, Dict{Step, SetPathNodesId}())
        ix = og.inc[x]
        for (l, ys) in og.inc[y]
            xl = get(ix, l, nothing)
            xl === nothing && continue
            s = get!(t, l, SetPathNodesId())
            for r in ys
                r in xl && push!(s, r)
            end
        end
    end
    return adj
end

sec_step(x :: PathNodeId) = x.id.step

function sec_fix!(adj :: SecAdj, nsteps :: Int) :: SecAdj
    changed = true
    #! [while] $ O(N*7) $
    while changed
        changed = false
        dead = [y for (y, t) in adj if any(l -> isempty(get(t, l, SetPathNodesId())), 0:nsteps-1)]
        for y in dead
            for (_, ws) in adj[y], w in ws
                w != y && haskey(adj, w) && delete!(get(adj[w], sec_step(y), SetPathNodesId()), y)
            end
            delete!(adj, y)
            changed = true
        end
        bad = Tuple{PathNodeId, PathNodeId}[]
        for (y, t) in adj, (_, ws) in t, w in ws
            (w == y || !haskey(adj, w) || PathOwnersGraph.node_ord(w) < PathOwnersGraph.node_ord(y)) && continue
            tw = adj[w]
            ok = all(0:nsteps-1) do s
                a = get(t, s, nothing); b = get(tw, s, nothing)
                a !== nothing && b !== nothing && any(r -> r in b, a)
            end
            ok || push!(bad, (y, w))
        end
        for (y, w) in bad
            delete!(adj[y][sec_step(w)], w); delete!(adj[w][sec_step(y)], y)
            changed = true
        end
    end
    return adj
end

sec_has(adj :: SecAdj, y, w) = haskey(adj, y) && w in get(adj[y], sec_step(w), SetPathNodesId())

# Lean `choiceAt`: en el paso k quedan vivos de dos nodos del mapa distintos.
choice_at(og :: OwnersGraph, k) = length(unique(x.id for x in get(og.alive, k, SetPathNodesId()))) >= 2

# Las aristas fuera de toda sección en algún paso con elección. by = :map (SecPair) o :node (SecPairX).
function sec_pair_bad(og :: OwnersGraph; by :: Symbol = :map) :: Vector{Tuple{PathNodeId, PathNodeId}}
    key = by == :map ? (x -> x.id) : identity
    bad = Set{Tuple{PathNodeId, PathNodeId}}()
    #! [for] $ O(S) $
    for k in 0:og.nsteps-1
        choice_at(og, k) || continue
        groups = Dict{Any, Vector{PathNodeId}}()
        for x in og.alive[k]
            push!(get!(groups, key(x), PathNodeId[]), x)
        end
        secs = [sec_fix!(sec_section(og, xs), og.nsteps) for xs in values(groups)]
        for e in values(og.edges)
            any(adj -> sec_has(adj, e.a, e.b), secs) || push!(bad, (e.a, e.b))
        end
    end
    return collect(bad)
end

sec_pair(gpath :: GPath; by :: Symbol = :map) :: Bool = isempty(sec_pair_bad(gpath.og; by))
