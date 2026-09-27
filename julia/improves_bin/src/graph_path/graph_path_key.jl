# 27-sept-2026
#
# Dos reglas sobre la fila de claves (informe docs/bitacora/verificacion_inseguridad_autor_v196.md §3 y §3.5).
#
# En un estado unido de la línea n+1 (cima n+1), la fila de claves es la del paso n = current_step - 2: cada nodo de esa
# fila viene de una sola pieza, la de su fuente (la clave). Por debajo, las tablas son la unión de las piezas.
#
# 1. Etiqueta de clave de un nivel (KEY_MODE). Cada entrada (p, v) de un nodo p por debajo de la fila de claves recuerda
#    de qué claves viene. Al fijar una clave k (filter_require! en la fila de claves), las filas de abajo se quedan con
#    las entradas etiquetadas k: exactamente las de la pieza k. Las etiquetas solo viven una línea: el UP siguiente las
#    sustituye. No pierde soluciones: una solución que pasa por k es un camino de la pieza k.
#
# 2. Comprobación de claves (KEYCHECK_MODE). En el punto fijo del review de un estado con dos o más claves vivas, cada
#    clave se fija en una copia; la que deja la copia inválida se quita de los owners globales (todas a la vez, contra el
#    mismo estado), y el review sigue. No pierde soluciones: si fijar k invalida el estado, ninguna pasa por k.
#
# Las dos están apagadas por defecto (:off): con :off la máquina es la de siempre.

const KEY_MODE = Ref(:off)
const KEYCHECK_MODE = Ref(:off)

# Contadores (solo para medir; no cambian nada).
const KEY_JOINS      = Ref(0)   # joins con etiquetas
const KEY_RESTRICTS  = Ref(0)   # fijaciones de clave sobre un estado unido
const KEY_CUT        = Ref(0)   # entradas quitadas por no llevar la etiqueta de la clave fijada
const KEYCHECK_COPIES  = Ref(0) # copias revisadas por la comprobación de claves
const KEYCHECK_REMOVED = Ref(0) # claves quitadas por la comprobación

function reset_key_counters!()
    KEY_JOINS[] = 0; KEY_RESTRICTS[] = 0; KEY_CUT[] = 0
    KEYCHECK_COPIES[] = 0; KEYCHECK_REMOVED[] = 0
end

# ============================================================
# 1. Etiqueta de clave
# ============================================================

# Tras el UP: la pieza entera es de una sola clave (etiqueta implícita, O(1)). Descarta las del nivel anterior.
function init_key_tags!(gpath :: GPath, key :: Union{NodeId, Nothing})
    if KEY_MODE[] == :on && key !== nothing
        gpath.key_tags = KeyTags(key.step, key, Dict{Tuple{PathNodeId, PathNodeId}, SetNodesId}())
    else
        gpath.key_tags = nothing
    end
end

# De implícita a explícita: toda entrada (p, v) con p bajo la fila de claves recibe la clave de la pieza.
function materialize_key_tags!(gpath :: GPath)
    kt = gpath.key_tags
    (kt === nothing || kt.single === nothing) && return
    key = kt.single
    #! [fn-iter] $ O(S*7*S*7) $
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        node.id.id.step < kt.key_step || return
        for (_, set) in node.owners.table, v in set
            kt.tags[(node.id, v)] = SetNodesId([key])
        end
    end)
    kt.single = nothing
end

# En el join, antes de unir las tablas: unión de etiquetas entrada a entrada. `other` es ya la copia del join.
# Si a alguno le faltan etiquetas (o no hablan de la misma fila), el estado unido se queda sin ellas: sin etiqueta,
# fijar la clave es el filtro de siempre.
function join_key_tags!(gpath :: GPath, other :: GPath)
    a = gpath.key_tags; b = other.key_tags
    if a === nothing || b === nothing || a.key_step != b.key_step
        gpath.key_tags = nothing
        return
    end
    KEY_JOINS[] += 1
    materialize_key_tags!(gpath)
    materialize_key_tags!(other)
    #! [for] $ O(S*7*S*7) $
    for (e, ks) in b.tags
        union!(get!(a.tags, e, SetNodesId()), ks)
    end
end

# Al fijar la clave k: las filas de abajo se quedan solo con las entradas de la pieza k. Un nodo que no está en la pieza
# pierde su propia entrada (su paso queda vacío) y lo purga el review.
function restrict_to_key!(gpath :: GPath, k :: NodeId)
    kt = gpath.key_tags
    (kt === nothing || kt.single !== nothing) && return    # sin join, ya es una sola pieza
    KEY_RESTRICTS[] += 1
    none = SetNodesId()
    #! [fn-iter] $ O(S*7*S*7) $
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        node.id.id.step < kt.key_step || return
        for (_, set) in node.owners.table, v in collect(set)
            k in Base.get(kt.tags, (node.id, v), none) && continue
            PathDocumentNode.remove_owner!(node, v)
            KEY_CUT[] += 1
            gpath.review_owners = true
        end
    end)
    gpath.key_tags = KeyTags(kt.key_step, k, empty(kt.tags))   # de aquí en adelante, pieza k
end

# ============================================================
# 2. Comprobación de claves
# ============================================================

key_step(gpath :: GPath) :: Step =
    gpath.key_tags !== nothing ? gpath.key_tags.key_step : gpath.current_step - 2

# Las claves vivas: nodos de mapa de los owners globales en la fila de claves.
function live_keys(gpath :: GPath) :: Vector{NodeId}
    ks = key_step(gpath)
    ks >= 0 || return NodeId[]
    ids = PathDocumentOwners.get(gpath.owners, ks)
    ids === nothing && return NodeId[]
    unique([pid.id for pid in ids])
end

# Fase 1: qué claves no sobreviven a su pin, todas contra el estado de ahora. Fase 2: se quitan a la vez.
# Devuelve true si quitó alguna (hay que repetir el review).
function key_check!(gpath :: GPath) :: Bool
    (KEYCHECK_MODE[] == :on && gpath.is_valid) || return false
    keys = live_keys(gpath)
    length(keys) >= 2 || return false

    dead = NodeId[]
    #! [for] $ O(K) $   K = claves vivas (≤ 2 en el mapa bin)
    for k in keys
        g = deepcopy(gpath)
        KEYCHECK_COPIES[] += 1
        # filter! = filter_require! (con etiquetas, restrict_to_key!) + review. En la copia queda una sola clave viva,
        # así que su propia comprobación no hace nada: no hay recursión.
        filter!(g, SetNodesId([k]))
        g.is_valid || push!(dead, k)
    end
    isempty(dead) && return false

    #! [for] $ O(K*7) $
    for k in dead
        for pid in collect(PathCollectionLines.get_ids_step(gpath.table_lines, k.step))
            pid.id == k && remove_node_owner!(gpath, pid)
        end
        KEYCHECK_REMOVED[] += 1
    end
    gpath.review_owners = true
    return true
end
