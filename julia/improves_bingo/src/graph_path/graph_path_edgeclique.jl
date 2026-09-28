# 28-sept-2026
#
# EdgeClique: todo lo vivo está en una camarilla válida (espejo de
# lean/improves_bingo/AbsSatBingo/Model/EdgeClique.lean). Consulta, no regla.
#
# Una camarilla llevada (Lean `Carried`) es una cadena de enlaces padre → hijo desde una raíz (paso 0) hasta la
# cima (current_step - 1), por nodos vivos con documento que se poseen dos a dos. edge_clique_miss enumera todas
# (DFS con poda por posesión) y devuelve (aristas sin cubrir, nodos sin cubrir), o nothing si hay más de `cap`
# cadenas. (0, 0) ⇔ EdgeClique.

function edge_clique_miss(gpath :: GPath; cap :: Int = 20000) :: Union{Nothing, Tuple{Int, Int}}
    og = gpath.og
    top = gpath.current_step - 1
    top < 0 && return (0, 0)
    covE = Set{Tuple{PathNodeId, PathNodeId}}()
    covV = SetPathNodesId()
    chain = PathNodeId[]
    chains = Ref(0)
    over = Ref(false)
    function ext(x)
        over[] && return
        push!(chain, x)
        if x.id.step == top
            chains[] += 1
            chains[] > cap && (over[] = true)
            for (i, a) in enumerate(chain)
                push!(covV, a)
                for j in i+1:length(chain)
                    push!(covE, PathOwnersGraph.edge_key(a, chain[j]))
                end
            end
        else
            n = PathCollectionLines.get_node(gpath.table_lines, x)
            if n !== nothing
                for s in n.sons
                    PathOwnersGraph.is_alive(og, s) || continue
                    PathCollectionLines.get_node(gpath.table_lines, s) === nothing && continue
                    all(a -> PathOwnersGraph.has_edge(og, a, s), chain) && ext(s)
                end
            end
        end
        pop!(chain)
    end
    for r in get(og.alive, 0, SetPathNodesId())
        r.parent_id === nothing || continue
        PathCollectionLines.get_node(gpath.table_lines, r) === nothing && continue
        ext(r)
        over[] && return nothing
    end
    e_miss = count(k -> !(k in covE), keys(og.edges))
    v_miss = count(x -> !(x in covV), (x for (_, xs) in og.alive for x in xs))
    return (e_miss, v_miss)
end

edge_clique(gpath :: GPath; cap :: Int = 20000) :: Bool = edge_clique_miss(gpath; cap) == (0, 0)
