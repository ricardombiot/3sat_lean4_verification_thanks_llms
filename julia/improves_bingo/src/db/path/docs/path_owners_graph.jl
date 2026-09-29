# Rama graph_owners, 27-sept-2026 (docs/plans/graph_owners.md). F1: el módulo solo, con tests;
# GPath todavía no lo usa.
#
# Grafo de owners de un gpath: la relación «x y w son compatibles» (hoy repartida en las tablas
# node.owners, una por nodo) guardada una sola vez, en el gpath. Es simétrica por construcción y
# reflexiva de forma implícita (x es owner de sí mismo, sin objeto Edge).
module PathOwnersGraph
    using Main.AbsSat.Alias: Step, NodeId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Undo

    # ---------- etiquetas por fila (informe v204 §7; rama row-tags) ----------
    # Cada arista (y cada nodo, por su arista reflexiva) guarda, por cada fila de claves ℓ, la máscara de las
    # claves (nodos del mapa del paso ℓ) de cuyas piezas viene: bit i ⇔ la clave (ℓ, i). Una fila de claves es el
    # paso de la cima de un remitente: la llegada la marca con {k} (`stamp!`), el UP hereda de los padres y el join
    # une fila a fila. La regla que las usa está en graph_path_tags.jl.
    #
    # ROW_TAGS: :off (por defecto; no se guarda nada) | :on. Variable de entorno ROW_TAGS.
    const ROW_TAGS = Ref(Symbol(get(ENV, "ROW_TAGS", "off")))
    tags_on() = ROW_TAGS[] == :on

    const Mask = UInt8
    const NOKEY = 0x00
    const Tags = Vector{Mask}
    const EMPTY_TAGS = Mask[]        # compartida por todas las aristas con ROW_TAGS = :off; nunca se modifica
    key_bit(k :: NodeId) :: Mask = (@assert 0 <= k.index < 8 "clave con índice $(k.index) ≥ 8"; Mask(1) << k.index)

    # ---------- arista ----------
    # Una compatibilidad (a, b), a ≺ b. Mutable: aquí irán los datos propios de cada arista
    # (contadores de apoyo, marcas de las reglas nuevas…).
    mutable struct Edge
        a :: PathNodeId
        b :: PathNodeId
        born :: Step                  # paso en que se creó (para medir)
        tags :: Tags                  # máscara de claves por fila (vacía con ROW_TAGS = :off)
    end
    Edge(a, b, born) = Edge(a, b, born, EMPTY_TAGS)

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
        ntags   :: Dict{PathNodeId, Tags}            # etiquetas de la arista reflexiva de cada vivo
        krows   :: Int                               # filas de claves marcadas: las filas 0 … krows-1
    end

    OwnersGraph(alive, edges, inc, nsteps, valid) = OwnersGraph(alive, edges, inc, nsteps, valid, Dict(), 0)
    new() = OwnersGraph(Dict(), Dict(), Dict(), 0, true)

    # Las etiquetas del par (x, w): la reflexiva es la del nodo.
    tags_of(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId) :: Tags =
        x == w ? g.ntags[x] : g.edges[edge_key(x, w)].tags
    has_key(t :: Tags, ℓ :: Int, a :: Mask) :: Bool = (t[ℓ + 1] & a) != NOKEY

    # La llegada del remitente de clave k: toda arista y todo nodo de la copia vienen de la pieza k en la fila
    # k.step, que es la siguiente por marcar.
    function stamp!(g :: OwnersGraph, k :: NodeId)
        tags_on() || return
        @assert k.step == g.krows "fila de claves fuera de orden: $(k.step) ≠ $(g.krows)"
        b = key_bit(k)
        for e in values(g.edges); push!(e.tags, b); end
        for t in values(g.ntags); push!(t, b); end
        g.krows += 1
        Undo.active() && Undo.record!(function ()
            g.krows -= 1
            for e in values(g.edges); pop!(e.tags); end
            for t in values(g.ntags); pop!(t); end
        end)
    end

    # Aristas quitadas por cada regla, en todo el proceso (solo para medir). Global y no por grafo: el
    # grafo se copia en cada UP y se une en los joins, y un contador suyo contaría varias veces.
    const REMOVED_BY = Dict{Symbol, Int}()

    step_of(id :: PathNodeId) = id.id.step

    # ---------- vértices ----------
    function add_step!(g :: OwnersGraph)
        n = g.nsteps
        g.alive[n] = SetPathNodesId()
        g.nsteps += 1
        Undo.active() && Undo.record!(() -> (delete!(g.alive, n); g.nsteps = n))
    end

    function register!(g :: OwnersGraph, x :: PathNodeId, tags :: Union{Nothing, Tags} = nothing)
        if Undo.active()
            s = step_of(x)
            line_new = !haskey(g.alive, s)
            Undo.record!(function ()
                delete!(g.alive[s], x)
                line_new && delete!(g.alive, s)
                delete!(g.inc, x)
                delete!(g.ntags, x)
            end)
        end
        push!(get!(g.alive, step_of(x), SetPathNodesId()), x)
        g.inc[x] = Inc(step_of(x) => SetPathNodesId([x]))   # reflexiva, sin objeto Edge
        tags_on() && (g.ntags[x] = tags === nothing ? zeros(Mask, g.krows) : copy(tags))
    end

    is_alive(g, x) = haskey(g.inc, x)

    # Quita x de V y todas sus aristas (hoy: remove_node_owner! + fase 2 de clean + espejo).
    function remove_node!(g :: OwnersGraph, x :: PathNodeId; rule :: Symbol = :node)
        is_alive(g, x) || return
        for w in collect(neighbors_all(g, x))
            w == x || remove_edge!(g, x, w; rule)
        end
        if Undo.active()
            inc_x = g.inc[x]; nt_x = get(g.ntags, x, nothing); valid = g.valid
            line0 = g.alive[step_of(x)]
            Undo.record!(function ()
                g.inc[x] = inc_x
                nt_x === nothing || (g.ntags[x] = nt_x)
                push!(line0, x)
                g.valid = valid
            end)
        end
        delete!(g.inc, x)
        delete!(g.ntags, x)
        line = g.alive[step_of(x)]
        delete!(line, x)
        isempty(line) && (g.valid = false)
    end

    # ---------- aristas ----------
    # Con etiquetas, una arista que ya estaba une las suyas con `tags` fila a fila.
    function add_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId, tags :: Union{Nothing, Tags} = nothing)
        x == w && return nothing
        k = edge_key(x, w)
        e = get(g.edges, k, nothing)
        if e !== nothing
            if tags_on() && tags !== nothing
                if Undo.active()
                    old = copy(e.tags)
                    Undo.record!(() -> copyto!(e.tags, old))
                end
                e.tags .|= tags
            end
            return e
        end
        e = Edge(k[1], k[2], g.nsteps - 1,
                 !tags_on() ? EMPTY_TAGS : tags === nothing ? zeros(Mask, g.krows) : copy(tags))
        g.edges[k] = e
        if Undo.active()
            ix = g.inc[x]; iw = g.inc[w]; sw = step_of(w); sx = step_of(x)
            new_x = !haskey(ix, sw); new_w = !haskey(iw, sx)
            Undo.record!(function ()
                delete!(g.edges, k)
                delete!(ix[sw], w); new_x && delete!(ix, sw)
                delete!(iw[sx], x); new_w && delete!(iw, sx)
            end)
        end
        push!(get!(g.inc[x], step_of(w), SetPathNodesId()), w)
        push!(get!(g.inc[w], step_of(x), SetPathNodesId()), x)
        return e
    end

    function remove_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId; rule :: Symbol)
        x == w && return false
        k = edge_key(x, w)
        haskey(g.edges, k) || return false
        e = g.edges[k]
        delete!(g.edges, k)
        dx = _drop!(g.inc[x], w)
        dw = _drop!(g.inc[w], x)
        Undo.active() && Undo.record!(function ()
            g.edges[k] = e
            dx && push!(g.inc[x][step_of(w)], w)
            dw && push!(g.inc[w][step_of(x)], x)
        end)
        REMOVED_BY[rule] = get(REMOVED_BY, rule, 0) + 1
        return true
    end

    # La línea vacía se queda: is_valid_owners la ve (como hoy empty_steps).
    function _drop!(inc :: Inc, w :: PathNodeId)
        ws = get(inc, step_of(w), nothing)
        (ws === nothing || !(w in ws)) && return false
        delete!(ws, w)
        return true
    end

    # Por la incidencia (una búsqueda en Dict y otra en Set), sin construir la clave de la arista:
    # es la consulta más frecuente del review. La incidencia y `edges` coinciden (check_invariants).
    function has_edge(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId) :: Bool
        inc = get(g.inc, x, nothing)
        inc === nothing && return false
        ws = get(inc, step_of(w), nothing)
        return ws !== nothing && w in ws
    end
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
    # Solo pasos anteriores al de n: un hermano ya registrado está en la tabla del padre común, pero
    # hoy los hermanos nunca se poseen (se crean todos antes de registrar ninguno).
    # Etiquetas: el nodo nuevo, la unión de las de sus padres; la arista n–w, la unión de las de p–w.
    function create_from_parents!(g :: OwnersGraph, n :: PathNodeId, parents)
        if tags_on()
            nt = zeros(Mask, g.krows)
            for p in parents; nt .|= g.ntags[p]; end
            register!(g, n, nt)
        else
            register!(g, n)
        end
        for p in parents, w in collect(neighbors_all(g, p))
            step_of(w) < step_of(n) && is_alive(g, w) &&
                (tags_on() ? add_edge!(g, n, w, tags_of(g, p, w)) : add_edge!(g, n, w))
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
    # Etiquetas: fila a fila, OR (los dos llegan al mismo destino, con las mismas filas marcadas).
    function union!(ga :: OwnersGraph, gb :: OwnersGraph)
        tags_on() && @assert ga.krows == gb.krows "join con filas de claves distintas: $(ga.krows) ≠ $(gb.krows)"
        for (step, ids) in gb.alive, x in ids
            if !is_alive(ga, x)
                tags_on() ? register!(ga, x, gb.ntags[x]) : register!(ga, x)
            elseif tags_on()
                ga.ntags[x] .|= gb.ntags[x]
            end
        end
        for e in values(gb.edges)
            tags_on() ? add_edge!(ga, e.a, e.b, e.tags) : add_edge!(ga, e.a, e.b)
        end
        ga.nsteps = max(ga.nsteps, gb.nsteps)
    end

    # ---------- copia ----------
    # El grafo solo guarda ids (inmutables) en Dicts y Sets, sin referencias cruzadas: se copia por
    # estructura, sin el IdDict del deepcopy genérico. Es la copia de cada UP (sat_machine.jl, send_to_destine!).
    # Los Dict se copian enteros (sin volver a hashear) y luego se sustituyen sus valores en su sitio con map!.
    function copy_graph(g :: OwnersGraph) :: OwnersGraph
        alive = copy(g.alive);  map!(copy, values(alive))
        edges = copy(g.edges);  map!(e -> Edge(e.a, e.b, e.born, tags_on() ? copy(e.tags) : EMPTY_TAGS), values(edges))
        inc = copy(g.inc)
        map!(values(inc)) do r
            r2 = copy(r); map!(copy, values(r2)); r2
        end
        ntags = copy(g.ntags);  map!(copy, values(ntags))
        return OwnersGraph(alive, edges, inc, g.nsteps, g.valid, ntags, g.krows)
    end

    Base.deepcopy_internal(g :: OwnersGraph, stackdict :: IdDict) =
        get!(() -> copy_graph(g), stackdict, g)

    # ---------- invariantes ----------
    # La primera violación encontrada, o nothing. Para tests y asserts:
    #   · cada arista está bajo su clave, une dos vivos y aparece en la incidencia de los dos;
    #   · cada vecino w ≠ x de la incidencia de x tiene su arista (luego la relación es simétrica);
    #   · cada vivo está en `alive` de su paso y en su propia incidencia (reflexiva), y al revés.
    function invariant_violation(g :: OwnersGraph) :: Union{Nothing, String}
        for (k, e) in g.edges
            k == edge_key(e.a, e.b) || return "arista bajo una clave que no es la suya: $k"
            e.a != e.b || return "arista reflexiva con objeto: $k"
            (is_alive(g, e.a) && is_alive(g, e.b)) || return "arista con un extremo muerto: $k"
            e.b in neighbors(g, e.a, step_of(e.b)) || return "falta b en la incidencia de a: $k"
            e.a in neighbors(g, e.b, step_of(e.a)) || return "falta a en la incidencia de b: $k"
        end
        for (x, inc) in g.inc
            x in get(g.alive, step_of(x), SetPathNodesId()) || return "vivo fuera de alive: $x"
            x in get(inc, step_of(x), SetPathNodesId()) || return "falta la reflexiva: $x"
            for (step, ws) in inc, w in ws
                step_of(w) == step || return "vecino en la línea de otro paso: $x ~ $w"
                w == x && continue
                haskey(g.edges, edge_key(x, w)) || return "vecino sin arista: $x ~ $w"
            end
        end
        for (_, ids) in g.alive, x in ids
            is_alive(g, x) || return "en alive sin incidencia: $x"
        end
        if tags_on()
            for (k, e) in g.edges
                length(e.tags) == g.krows || return "arista con $(length(e.tags)) filas de etiquetas, no $(g.krows): $k"
            end
            for x in keys(g.inc)
                t = get(g.ntags, x, nothing)
                (t !== nothing && length(t) == g.krows) || return "nodo sin sus $(g.krows) filas de etiquetas: $x"
            end
            length(g.ntags) == length(g.inc) || return "etiquetas de nodos muertos"
        end
        return nothing
    end

    check_invariants(g :: OwnersGraph) :: Bool = invariant_violation(g) === nothing

    # ---------- puente con la representación actual (test diferencial) ----------
    as_table(g :: OwnersGraph, x :: PathNodeId) :: Inc = deepcopy(g.inc[x])
end
