# 27-sept-2026
#
# Etiquetas de clave de todos los niveles (informe docs/bitacora/verificacion_inseguridad_autor_v197.md §5).
#
# Cada UP convierte la fila de la fuente en una fila de claves: la pieza viene de una sola clave (el nodo de mapa de la
# fuente). El join une piezas de claves distintas y sus tablas se mezclan. La etiqueta recuerda, por cada entrada (p, v)
# de una tabla y cada fila de claves ℓ por la que pasó, de qué claves venía: una máscara con un bit por nodo de mapa de
# esa fila (bit i ⇔ nodo de mapa (ℓ, i)).
#
#   * UP:   la fila de la fuente entra con una sola clave (máscara uniforme); las filas anteriores se heredan; el nodo
#           nuevo hereda de sus padres (OR) y su espejo copia la suya.
#   * join: fila a fila, OR de máscaras; una fila en que las dos máscaras uniformes difieren se materializa por entrada.
#   * pin:  fijar la clave k en su fila ℓ (filter_require!) deja en cada tabla solo las entradas que llevan k en ℓ.
#   * review: sin cambios (las máscaras de entradas quitadas se limpian en el UP siguiente).
#
# No pierde soluciones: una solución que pasa por k en la fila ℓ es un camino de la pieza k de esa línea, así que todas
# sus entradas llevan k.
#
#   :off — (por defecto) la máquina de siempre.
#   :on  — la regla.

const KEYTAGS_MODE = Ref(:off)

# Contadores (solo para medir; no cambian nada).
const KEYTAGS_CUT        = Ref(0)   # entradas quitadas por no llevar la clave fijada
const KEYTAGS_RESTRICTS  = Ref(0)   # fijaciones sobre una fila mezclada
const KEYTAGS_MATERIAL   = Ref(0)   # filas materializadas (dejan de ser uniformes)
const KEYTAGS_MISSING    = Ref(0)   # entradas sin máscara en una fila mezclada (debería ser 0)
const KEYTAGS_DROPPED    = Ref(0)   # filas descartadas en un join por faltar en un lado (debería ser 0)

function reset_keytags_counters!()
    KEYTAGS_CUT[] = 0; KEYTAGS_RESTRICTS[] = 0; KEYTAGS_MATERIAL[] = 0
    KEYTAGS_MISSING[] = 0; KEYTAGS_DROPPED[] = 0
end

const Entry = Tuple{PathNodeId, PathNodeId}

key_bit(k :: NodeId) :: KeyMask = KeyMask(1) << k.index

# Las entradas (p, v) del estado.
#! [fn-iter] $ O(S*7 * S*7) $
function entries(gpath :: GPath) :: Vector{Entry}
    es = Entry[]
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        for (_, set) in node.owners.table, v in set
            push!(es, (node.id, v))
        end
    end)
    es
end

# La máscara de la entrada (p, v) en la fila ℓ (`nothing` si la fila no tiene etiqueta).
function tag_mask(t :: KeyTagsAll, e :: Entry, ℓ :: Step) :: Union{KeyMask, Nothing}
    m = get(t.mixed, ℓ, nothing)
    m !== nothing && return get(m, e, nothing)
    get(t.uniform, ℓ, nothing)
end

# ============================================================
# UP
# ============================================================

# Las máscaras de entradas que la review ya quitó.
#! [for] $ O(L_mix * S*7 * S*7) $
function prune_keytags!(gpath :: GPath)
    t = gpath.key_tags
    (t === nothing || isempty(t.mixed)) && return
    alive = Set(entries(gpath))
    for (_, m) in t.mixed
        Base.filter!(((e, _),) -> e in alive, m)
    end
end

# El nodo nuevo del UP hereda, en cada fila mezclada, la máscara de sus padres (OR): la de (padre, v) para cada entrada
# (nuevo, v), y la de (padre, padre) para la suya propia. El espejo (v, nuevo) lleva la misma máscara.
#! [for] $ O(L_mix * 7 * S*7) $ por nodo nuevo
function inherit_keytags!(gpath :: GPath, node :: PathDocNode)
    t = gpath.key_tags
    (t === nothing || isempty(t.mixed)) && return
    for (_, m) in t.mixed
        for (_, set) in node.owners.table, v in set
            mask = KeyMask(0)
            for c in node.parents
                src = v == node.id ? (c, c) : (c, v)
                mask |= get(m, src, KeyMask(0))
            end
            m[(node.id, v)] = mask
            m[(v, node.id)] = mask
        end
    end
end

# Tras el UP: la fila de la fuente pasa a ser fila de claves, con una sola clave.
function init_key_level!(gpath :: GPath, key :: Union{NodeId, Nothing})
    if KEYTAGS_MODE[] != :on || key === nothing || key.index >= 8 * sizeof(KeyMask)
        gpath.key_tags = nothing
        return
    end
    t = gpath.key_tags === nothing ? KeyTagsAll(Dict{Step, KeyMask}(), Dict{Step, Dict{Entry, KeyMask}}()) : gpath.key_tags
    t.uniform[key.step] = key_bit(key)
    gpath.key_tags = t
end

# ============================================================
# Join
# ============================================================

# Una fila deja de ser uniforme: se materializa entrada a entrada.
#! [fn-iter] $ O(S*7 * S*7) $
function materialize_level!(gpath :: GPath, ℓ :: Step)
    t = gpath.key_tags
    haskey(t.mixed, ℓ) && return
    u = t.uniform[ℓ]
    t.mixed[ℓ] = Dict{Entry, KeyMask}(e => u for e in entries(gpath))
    delete!(t.uniform, ℓ)
    KEYTAGS_MATERIAL[] += 1
end

levels(t :: KeyTagsAll) = union(keys(t.uniform), keys(t.mixed))

# Antes de unir las tablas; `other` es ya la copia del join. Fila a fila, OR de máscaras.
#! [for] $ O(L * S*7 * S*7) $ peor caso; O(L) si ninguna fila se mezcla de nuevo
function join_keytags!(gpath :: GPath, other :: GPath)
    a = gpath.key_tags; b = other.key_tags
    if a === nothing || b === nothing
        gpath.key_tags = nothing
        return
    end
    for ℓ in collect(levels(a))
        if !(ℓ in levels(b))                        # no debería pasar: los estados de una línea tienen las mismas filas
            delete!(a.uniform, ℓ); delete!(a.mixed, ℓ); KEYTAGS_DROPPED[] += 1
        end
    end
    for ℓ in levels(b)
        ℓ in levels(a) || (KEYTAGS_DROPPED[] += 1; continue)
        if haskey(a.uniform, ℓ) && haskey(b.uniform, ℓ) && a.uniform[ℓ] == b.uniform[ℓ]
            continue                                # fila sin mezcla nueva
        end
        materialize_level!(gpath, ℓ)
        materialize_level!(other, ℓ)
        ma = a.mixed[ℓ]
        for (e, mask) in b.mixed[ℓ]
            ma[e] = get(ma, e, KeyMask(0)) | mask
        end
    end
end

# ============================================================
# Pin
# ============================================================

# Fijar la clave k en su fila: cada tabla se queda con las entradas que llevan k en esa fila.
#! [fn-iter] $ O(S*7 * S*7) $
function restrict_keytags!(gpath :: GPath, k :: NodeId)
    t = gpath.key_tags
    t === nothing && return
    ℓ = k.step
    if haskey(t.uniform, ℓ)
        # una sola historia en esa fila: si no es la de k, el pin ya deja la fila sin nodos
        t.uniform[ℓ] &= key_bit(k)
        return
    end
    m = get(t.mixed, ℓ, nothing)
    m === nothing && return
    KEYTAGS_RESTRICTS[] += 1
    bit = key_bit(k)
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        for (_, set) in node.owners.table, v in collect(set)
            mask = get(m, (node.id, v), nothing)
            if mask === nothing
                KEYTAGS_MISSING[] += 1
                continue                            # sin máscara: se deja (permisivo)
            end
            (mask & bit) != 0 && continue
            PathDocumentNode.remove_owner!(node, v)
            KEYTAGS_CUT[] += 1
            gpath.review_owners = true
        end
    end)
    delete!(t.mixed, ℓ)
    t.uniform[ℓ] = bit
end
