# Consultas sobre el grafo de owners de un gpath (plan docs/plans/graph_owners.md, F3), para tests,
# visual y diferenciales. La máquina no las necesita: usa PathOwnersGraph directamente.

# ¿Sigue x en el grafo? (antes: x en la global, gpath.owners)
is_alive(gpath :: GPath, x :: PathNodeId) :: Bool = PathOwnersGraph.is_alive(gpath.og, x)

# ¿Posee x a w? Simétrica y reflexiva. (antes: w en la tabla de x)
is_owner(gpath :: GPath, x :: PathNodeId, w :: PathNodeId) :: Bool =
    PathOwnersGraph.has_edge(gpath.og, x, w)

# La tabla de x en el formato de antes (paso => conjunto de ids), o nothing si x ya no está.
function owners_table(gpath :: GPath, x :: PathNodeId) :: Union{Nothing, Dict{Step, SetPathNodesId}}
    is_alive(gpath, x) || return nothing
    return PathOwnersGraph.as_table(gpath.og, x)
end

# Los vivos (antes: las entradas de la global).
alive_ids(gpath :: GPath) :: SetPathNodesId =
    reduce(union, values(gpath.og.alive); init = SetPathNodesId())
