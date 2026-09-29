# Regla de la etiqueta (29-sept-2026; informe v204 §7, rama row-tags).
#
# Con ROW_TAGS = :on, cada arista y cada nodo llevan, por cada fila de claves ℓ, la máscara de las claves de cuyas
# piezas vienen (path_owners_graph.jl). La regla revisa cada pieza por separado: la clave a se queda en la fila ℓ de
# un nodo o de una arista solo si las reglas de siempre se cumplen usando solo aristas que llevan a en la fila ℓ.
#
#   nodo x:      en cada paso, un vecino r con a en x–r; un padre (si no es raíz) y un hijo (si no es cima)
#                enlazados con a en la arista del enlace.
#   arista x–w:  a en los dos extremos; en cada paso, un testigo r con a en x–r y en w–r (regla de parejas);
#                para cada extremo u y el otro v, un padre p de u (si u no es raíz) con a en u–p y en p–v, y un
#                hijo s (si u no es cima) con a en u–s y en s–v (pasadas de padres e hijos).
#
# Un nodo o una arista que se queda sin claves en alguna fila muere. En dos fases, como la regla de parejas: se
# marcan todas las claves que caen con el estado de antes y se quitan a la vez; el review sigue hasta el punto fijo.
#
# Solidez (deducida, v204 §7.3): una solución pasa en la fila ℓ por una sola clave a; su camarilla es un camino de
# la pieza a, así que todas sus aristas y nodos llevan a en la fila ℓ, y sus propios nodos son los testigos, padres
# e hijos que la regla pide. La regla nunca quita a de ella.
#
# Solo se miran las filas mezcladas (alguna clave distinta entre los vivos): en una fila con una sola clave la regla
# es la de siempre.

# TAG_RULE: :on (por defecto) | :off, para medir: con :off se guardan y propagan las etiquetas pero la regla no
# corre (control negativo de probe_row_tags_union.jl). Variable de entorno TAG_RULE.
const TAG_RULE = Ref(Symbol(get(ENV, "TAG_RULE", "on")))
const TAG_RUNS = Ref(0)         # pasadas de la regla
const TAG_ROWS = Ref(0)         # filas mezcladas miradas (suma sobre pasadas)
const TAG_BITS_CUT = Ref(0)     # claves quitadas (nodo o arista, fila)
const TAG_EDGES_CUT = Ref(0)    # aristas muertas por la regla
const TAG_NODES_CUT = Ref(0)    # nodos muertos por la regla

const PG_ = PathOwnersGraph

function tag_mixed_rows(og :: OwnersGraph) :: Vector{Int}
    rows = Int[]
    for ℓ in 0:og.krows-1
        m = PG_.NOKEY
        for t in values(og.ntags)
            m |= t[ℓ + 1]
            if count_ones(m) >= 2
                push!(rows, ℓ)
                break
            end
        end
    end
    return rows
end

# La pieza de la clave a en la fila ℓ: los vivos que llevan a y, para cada uno, sus vecinos por aristas que llevan a,
# por paso (con la reflexiva). Las comprobaciones de la regla son entonces intersecciones de conjuntos, como en la
# regla de parejas de siempre (shares_every_step).
const TagSub = Dict{PathNodeId, Dict{Int, SetPathNodesId}}

function tag_sub(og :: OwnersGraph, ℓ :: Int, a :: PG_.Mask) :: TagSub
    sub = TagSub()
    for (x, t) in og.ntags
        PG_.has_key(t, ℓ, a) && (sub[x] = Dict(Int(x.id.step) => SetPathNodesId([x])))
    end
    for e in values(og.edges)
        PG_.has_key(e.tags, ℓ, a) || continue
        sa = get(sub, e.a, nothing); sb = get(sub, e.b, nothing)
        (sa === nothing || sb === nothing) && continue          # la arista cae: le falta a en un extremo
        push!(get!(sa, Int(e.b.id.step), SetPathNodesId()), e.b)
        push!(get!(sb, Int(e.a.id.step), SetPathNodesId()), e.a)
    end
    return sub
end

in_sub(d, y) = (s = get(d, Int(y.id.step), nothing); s !== nothing && y in s)

# Un enlace u–p (padre o hijo) de la pieza cuyo otro extremo p llega a v dentro de la pieza.
tag_link_support(sub, links, du, v) =
    any(p -> in_sub(du, p) && in_sub(sub[p], v), links)

function tag_node_keeps(gpath :: GPath, sub :: TagSub, x :: PathNodeId) :: Bool
    og = gpath.og
    d = sub[x]
    for l in 0:og.nsteps-1
        s = get(d, l, nothing)
        (s === nothing || isempty(s)) && return false
    end
    node = PathCollectionLines.get_node(gpath.table_lines, x)
    node === nothing && return false
    PathDocumentNode.is_root(node) || tag_link_support(sub, node.parents, d, x) || return false
    Int(x.id.step) == og.nsteps - 1 || tag_link_support(sub, node.sons, d, x) || return false
    return true
end

function tag_edge_keeps(gpath :: GPath, sub :: TagSub, x :: PathNodeId, w :: PathNodeId) :: Bool
    og = gpath.og
    dx = get(sub, x, nothing); dw = get(sub, w, nothing)
    (dx === nothing || dw === nothing || !in_sub(dx, w)) && return false
    for l in 0:og.nsteps-1
        sx = get(dx, l, nothing); sw = get(dw, l, nothing)
        (sx === nothing || sw === nothing) && return false
        short, long = length(sx) <= length(sw) ? (sx, sw) : (sw, sx)
        any(r -> r in long, short) || return false
    end
    for (u, v, du) in ((x, w, dx), (w, x, dw))
        node = PathCollectionLines.get_node(gpath.table_lines, u)
        node === nothing && return false
        PathDocumentNode.is_root(node) || tag_link_support(sub, node.parents, du, v) || return false
        Int(u.id.step) == og.nsteps - 1 || tag_link_support(sub, node.sons, du, v) || return false
    end
    return true
end

bits_of(m :: PG_.Mask) = (PG_.Mask(1) << i for i in 0:7 if (m >> i) & 0x01 == 0x01)

# Una pasada de la regla. Devuelve true si quitó alguna clave (y entonces pide otra vuelta de review).
function tag_rule!(gpath :: GPath) :: Bool
    TAG_RUNS[] += 1
    og = gpath.og
    rows = tag_mixed_rows(og)
    TAG_ROWS[] += length(rows)
    isempty(rows) && return false

    node_clear = Tuple{PathNodeId, Int, PG_.Mask}[]
    edge_clear = Tuple{PG_.Edge, Int, PG_.Mask}[]
    for ℓ in rows
        present = PG_.NOKEY
        for t in values(og.ntags); present |= t[ℓ + 1]; end
        for a in bits_of(present)
            sub = tag_sub(og, ℓ, a)
            for x in keys(sub)
                tag_node_keeps(gpath, sub, x) || push!(node_clear, (x, ℓ, a))
            end
            for e in values(og.edges)
                PG_.has_key(e.tags, ℓ, a) || continue
                tag_edge_keeps(gpath, sub, e.a, e.b) || push!(edge_clear, (e, ℓ, a))
            end
        end
    end
    isempty(node_clear) && isempty(edge_clear) && return false

    TAG_BITS_CUT[] += length(node_clear) + length(edge_clear)
    for (x, ℓ, a) in node_clear
        t = og.ntags[x]
        if Undo.active(); old = t[ℓ + 1]; Undo.record!(() -> (t[ℓ + 1] = old)); end
        t[ℓ + 1] &= ~a
    end
    for (e, ℓ, a) in edge_clear
        if Undo.active(); old = e.tags[ℓ + 1]; Undo.record!(() -> (e.tags[ℓ + 1] = old)); end
        e.tags[ℓ + 1] &= ~a
    end

    dead_edges = [e for e in values(og.edges) if any(==(PG_.NOKEY), e.tags)]
    for e in dead_edges
        PG_.remove_edge!(og, e.a, e.b; rule = :tag) && (TAG_EDGES_CUT[] += 1)
    end
    dead_nodes = [x for (x, t) in og.ntags if any(==(PG_.NOKEY), t)]
    for x in dead_nodes
        TAG_NODES_CUT[] += 1
        remove_node_owner!(gpath, x; rule = :tag)
    end

    gpath.review_owners = true
    return true
end
