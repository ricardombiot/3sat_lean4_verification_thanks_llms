# Borrador (rama graph_owners, 27-sept-2026). Todavía no se incluye en DBDocuments ni lo usa GPath:
# véase docs/plans/graph_owners.md.
#
# Grafo de owners de un gpath: la relación «x y w son compatibles» (hoy repartida en las tablas
# node.owners, una por nodo) guardada una sola vez, en el gpath. Es simétrica por construcción y
# reflexiva de forma implícita (x es owner de sí mismo, sin objeto Edge).
module PathOwnersGraph
    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId

    # ---------- arista ----------
    # Una compatibilidad (a, b), a ≺ b. Mutable: aquí irán los datos propios de cada arista
    # (contadores de apoyo, marcas de las reglas nuevas…).
    mutable struct Edge
        a :: PathNodeId
        b :: PathNodeId
        born :: Step                  # paso en que se creó (para medir)
    end

    const EdgeKey = Tuple{PathNodeId, PathNodeId}

    # Orden total y determinista entre ids: (paso, índice) del id, luego padre, luego abuelo.
    _ord(n :: Nothing) = (-1, -1)
    _ord(n) = (n.step, n.index)
    node_ord(x :: PathNodeId) = (_ord(x.id), _ord(x.parent_id), _ord(x.gparent_id))

    edge_key(x :: PathNodeId, w :: PathNodeId) :: EdgeKey =
        node_ord(x) <= node_ord(w) ? (x, w) : (w, x)

    other(e :: Edge, x :: PathNodeId) = e.a == x ? e.b : e.a

    # ---------- grafo ----------
    const Inc = Dict{Step, SetPathNodesId}          # vecinos de un nodo, por paso

    mutable struct OwnersGraph
        alive   :: Dict{Step, SetPathNodesId}        # vértices vivos (hoy: gpath.owners)
        edges   :: Dict{EdgeKey, Edge}               # cada compatibilidad, una vez
        inc     :: Dict{PathNodeId, Inc}             # incidencia (hoy: node.owners)
        nsteps  :: Int                               # pasos creados (current_step)
        valid   :: Bool
        removed_by :: Dict{Symbol, Int}              # aristas quitadas por cada regla (medida)
    end

    new() = OwnersGraph(Dict(), Dict(), Dict(), 0, true, Dict())

    step_of(id :: PathNodeId) = id.id.step

    # ---------- vértices ----------
    function add_step!(g :: OwnersGraph)
        g.alive[g.nsteps] = SetPathNodesId()
        g.nsteps += 1
    end

    function register!(g :: OwnersGraph, x :: PathNodeId)
        push!(get!(g.alive, step_of(x), SetPathNodesId()), x)
        g.inc[x] = Inc(step_of(x) => SetPathNodesId([x]))   # reflexiva, sin objeto Edge
    end

    is_alive(g, x) = haskey(g.inc, x)

    # Quita x de V y todas sus aristas (hoy: remove_node_owner! + fase 2 de clean + espejo).
    function remove_node!(g :: OwnersGraph, x :: PathNodeId; rule :: Symbol = :node)
        is_alive(g, x) || return
        for w in collect(neighbors_all(g, x))
            w == x || remove_edge!(g, x, w; rule)
        end
        delete!(g.inc, x)
        line = g.alive[step_of(x)]
        delete!(line, x)
        isempty(line) && (g.valid = false)
    end

    # ---------- aristas ----------
    function add_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId)
        x == w && return nothing
        k = edge_key(x, w)
        e = get(g.edges, k, nothing)
        e === nothing || return e
        e = Edge(k[1], k[2], g.nsteps - 1)
        g.edges[k] = e
        push!(get!(g.inc[x], step_of(w), SetPathNodesId()), w)
        push!(get!(g.inc[w], step_of(x), SetPathNodesId()), x)
        return e
    end

    function remove_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId; rule :: Symbol)
        x == w && return false
        k = edge_key(x, w)
        haskey(g.edges, k) || return false
        delete!(g.edges, k)
        _drop!(g.inc[x], w)
        _drop!(g.inc[w], x)
        g.removed_by[rule] = get(g.removed_by, rule, 0) + 1
        return true
    end

    # La línea vacía se queda: is_valid_owners la ve (como hoy empty_steps).
    function _drop!(inc :: Inc, w :: PathNodeId)
        ws = get(inc, step_of(w), nothing)
        ws === nothing || delete!(ws, w)
    end

    has_edge(g, x, w) = x == w ? is_alive(g, x) : haskey(g.edges, edge_key(x, w))
    get_edge(g, x, w) = get(g.edges, edge_key(x, w), nothing)

    neighbors(g, x, step) = get(g.inc[x], step, SetPathNodesId())
    neighbors_all(g, x) = Iterators.flatten(values(g.inc[x]))

    # Aristas de x como objetos (sin la reflexiva).
    incident_edges(g, x) = (g.edges[edge_key(x, w)] for w in neighbors_all(g, x) if w != x)

    # Todas las aristas entre el paso i y el paso j (para reglas sobre pares de pasos).
    edges_between(g, i :: Step, j :: Step) =
        (g.edges[edge_key(x, w)] for x in g.alive[i] for w in neighbors(g, x, j) if w != x)

    # ---------- validez de la tabla (hoy: is_valid / is_valid_intersect) ----------
    # x tiene al menos un vecino vivo en cada paso creado. Un paso sin línea también invalida
    # (es lo que hoy hace la comparación de max_step).
    function is_valid_owners(g :: OwnersGraph, x :: PathNodeId) :: Bool
        inc = g.inc[x]
        all(step -> !isempty(get(inc, step, SetPathNodesId())), 0:g.nsteps-1)
    end

    # ---------- UP: nodo nuevo desde sus padres ----------
    # tabla(n) = (∪ tablas de padres) ∩ vivos, más n mismo; simétrica al construirla
    # (sustituye a create_node_from_parents! + its_owners_are_owned_by_me!).
    function create_from_parents!(g :: OwnersGraph, n :: PathNodeId, parents)
        register!(g, n)
        for p in parents, w in neighbors_all(g, p)
            is_alive(g, w) && add_edge!(g, n, w)
        end
    end

    # ---------- pasadas de padres / hijos ----------
    supported(g, supports, w) = any(p -> has_edge(g, p, w), supports)

    # Borra (x,w) si ningún nodo de `supports` tiene la arista (·,w). Devuelve cuántas quitó
    # (> 0 ⇒ review_owners = true). rule = :parents o :sons.
    function cut_by_support!(g :: OwnersGraph, x :: PathNodeId, supports; rule :: Symbol) :: Int
        drop = [w for w in neighbors_all(g, x) if w != x && !supported(g, supports, w)]
        for w in drop                                  # se borra después de recorrer
            remove_edge!(g, x, w; rule)
        end
        return length(drop)
    end

    # ---------- join ----------
    # Los ids son los mismos en los dos gpaths: V = V₁ ∪ V₂, E = E₁ ∪ E₂.
    # Si la arista está en los dos, se queda la de ga (aquí se decidirá cómo mezclar sus datos).
    function union!(ga :: OwnersGraph, gb :: OwnersGraph)
        for (step, ids) in gb.alive, x in ids
            is_alive(ga, x) || register!(ga, x)
        end
        for e in values(gb.edges)
            add_edge!(ga, e.a, e.b)
        end
        ga.nsteps = max(ga.nsteps, gb.nsteps)
    end

    # ---------- puente con la representación actual (test diferencial) ----------
    as_table(g :: OwnersGraph, x :: PathNodeId) :: Inc = deepcopy(g.inc[x])
end
