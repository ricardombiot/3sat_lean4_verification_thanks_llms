# Regla de los tríos prohibidos (30-sept-2026, rama reader-stuck; informe v213).
#
# Con FORBID = :on, cada arista guarda los tríos prohibidos que la contienen (path_owners_graph.jl): r ∈ forbid(a,b)
# ⟺ ninguna solución pasa por a, b y r. El UP y el join los heredan; esta regla los descubre en el review:
#
#   trío (a, b, r):  se prohíbe si en algún paso no tiene testigo bueno: un s vecino de los tres con ninguno de los
#                    tríos (a,b,s), (a,r,s), (b,r,s) prohibido.
#   arista a–b:      muere si en algún paso no tiene testigo bueno: un r vecino de los dos con (a,b,r) no prohibido.
#
# Es TRIO_RULE con memoria. Solidez: el nodo de una solución en cada paso es testigo bueno de todo trío y de toda
# arista de la solución, así que la regla no prohíbe ningún trío de una solución ni corta ninguna de sus aristas.
# En dos fases, como la regla de parejas: se marca contra el estado de antes y se aplica todo a la vez.

const FORBID_TRIOS = Ref(0)     # tríos prohibidos por la regla (no los heredados del UP y del join)
const FORBID_EDGES = Ref(0)     # aristas muertas por la regla
const FORBID_ROUNDS = Ref(0)

good_witness(g, a, b, r, s) :: Bool =
    s == a || s == b || s == r ||
    (PG_.has_edge(g, a, s) && PG_.has_edge(g, b, s) && PG_.has_edge(g, r, s) &&
     !PG_.dead_trio(g, a, b, s) && !PG_.dead_trio(g, a, r, s) && !PG_.dead_trio(g, b, r, s))

function trio_alive(g, a, b, r) :: Bool
    #! [for] $ O(S*7) $
    for (_, sa) in g.inc[a]
        any(s -> good_witness(g, a, b, r, s), sa) || return false
    end
    return true
end

function edge_alive(g, a, b) :: Bool
    #! [for] $ O(S*7) $
    for (_, sa) in g.inc[a]
        any(r -> r == a || r == b || (PG_.has_edge(g, b, r) && !PG_.dead_trio(g, a, b, r)), sa) || return false
    end
    return true
end

function forbid_rule!(gpath :: GPath)
    og = gpath.og
    changed = true
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        FORBID_ROUNDS[] += 1
        # fase 1: tríos nuevos (cada trío una vez: a ≺ b ≺ r)
        trios = NTuple{3, PathNodeId}[]
        #! [for] $ O(|E|*N*S*7) $
        for e in values(og.edges), r in PG_.neighbors_all(og, e.a)
            (r == e.a || r == e.b || !(PG_.node_ord(e.b) < PG_.node_ord(r))) && continue
            PG_.has_edge(og, e.b, r) || continue
            PG_.dead_trio(og, e.a, e.b, r) && continue
            trio_alive(og, e.a, e.b, r) || push!(trios, (e.a, e.b, r))
        end
        for (a, b, r) in trios
            PG_.forbid!(og, a, b, r) && (FORBID_TRIOS[] += 1; changed = true)
        end
        # fase 2: aristas sin testigo bueno
        bad = [(e.a, e.b) for e in values(og.edges) if !edge_alive(og, e.a, e.b)]
        for (a, b) in bad
            PathOwnersGraph.remove_edge!(og, a, b; rule = :forbid)
            FORBID_EDGES[] += 1
        end
        if !isempty(bad)
            changed = true
            gpath.review_owners = true
            clean_invalid_nodes!(gpath)
        end
    end
end
