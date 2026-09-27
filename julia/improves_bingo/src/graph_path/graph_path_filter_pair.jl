# 24-sept-2026
#
# Regla de parejas tras la limpieza (informe v185 §5, plan docs/plans/pair_mode.md A2).
#
# Si dos nodos vivos x, w se poseen y en algún paso sus tablas no comparten ninguna entrada, ninguna
# solución pasa por los dos: la posesión se deshace en las dos direcciones. Es la rama «inconsistente»
# de agressive_consistence_filter!, adelantada a justo después de clean_invalid_nodes!, que es donde
# el pin deja los tramos sin entrada común.
#
# En dos fases, como la limpieza: con las tablas tal como están se marcan todas las parejas malas, se
# quitan todas a la vez, se purga, y se repite mientras algo cambie. Así el resultado no depende del
# orden en que se recorren los nodos (el de un Set es el del hash), y coincide con el modelo Lean
# (pairSweep: un map contra el estado de antes).
#
#   :off — (por defecto hasta medir) el review de siempre.
#   :on  — make_review_owners! llama a pair_consistency_after_clean! tras clean_invalid_nodes!.
const PAIR_MODE = Ref(:on)

# Contadores (solo para medir; no cambian nada).
const PAIR_REMOVED = Ref(0)     # parejas deshechas (cada arista cuenta una vez)
const PAIR_ROUNDS  = Ref(0)     # vueltas regla + purga

# ¿Comparten las tablas de x y w al menos una entrada en cada paso que tienen las dos?
# (antes PathDocumentOwners.shares_every_step; una línea vacía cuenta como paso sin entrada común)
function shares_every_step(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId) :: Bool
    inc_w = g.inc[w]
    #! [for] $ O(S) $
    for (step, set_x) in g.inc[x]
        set_w = get(inc_w, step, nothing)
        set_w === nothing && continue
        short, long = length(set_x) <= length(set_w) ? (set_x, set_w) : (set_w, set_x)
        #! [fixed] $ O(7) $
        any(id -> id in long, short) || return false
    end
    return true
end

function pair_consistency_after_clean!(gpath :: GPath)
    og = gpath.og
    changed = true
    #! [while] $ O(N*7) $ vueltas como mucho: cada vuelta que sigue ha deshecho al menos una pareja
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        PAIR_ROUNDS[] += 1

        # Fase 1: las parejas malas, contra el estado de ahora. Cada arista se mira una vez.
        bad = Tuple{PathNodeId, PathNodeId}[]
        #! [for] $ O(|E|*S*7) $
        for e in values(og.edges)
            shares_every_step(og, e.a, e.b) || push!(bad, (e.a, e.b))
        end

        # Fase 2: se quitan todas.
        #! [for] $ O(|bad|) $
        for (x_id, w_id) in bad
            PathOwnersGraph.remove_edge!(og, x_id, w_id; rule = :pair)
            PAIR_REMOVED[] += 1
            changed = true
        end

        if changed
            gpath.review_owners = true
            # purga: deshacer una pareja puede dejar un paso vacío
            clean_invalid_nodes!(gpath)
        end
    end
end
