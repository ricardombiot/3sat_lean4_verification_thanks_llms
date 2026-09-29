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

# Regla de tríos (29-sept-2026, rama reader-stuck; sonda dump_colour_helly.jl). Un trío muerto (x, w, z se poseen
# dos a dos pero sus tablas no comparten entrada en algún paso) no está en ninguna solución, y aun así la regla de
# parejas lo deja servir de testigo. Con TRIO_RULE la regla de parejas pide testigos buenos: la arista x–w sobrevive si
# en cada paso comparten una entrada r con la que el trío (x, w, r) tiene entrada común en cada paso. No pierde
# soluciones: el nodo de una solución en cada paso es un testigo bueno (los tres están en la solución).
# No borra el trío (sus parejas pueden tener otros testigos): el grafo de posesiones no puede decir «estos tres no».
#   :off    — (por defecto) la regla de parejas de siempre.
#   :on     — el trío se comprueba en todos los pasos.
#   :clause — el trío se comprueba solo en los pasos de cláusula (TRIO_STEPS, lo fija la máquina con el mapa bin).
const TRIO_RULE = Ref(Symbol(get(ENV, "TRIO_RULE", "off")))
const TRIO_STEPS = Ref{Union{Nothing, Set{Step}}}(nothing)
const TRIO_REMOVED = Ref(0)     # aristas que corta la regla de tríos y no la de parejas

# ¿Tienen x, w y r una entrada común en cada paso de `steps` (nothing: todos) que tienen los tres?
function trio_ok(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId, r :: PathNodeId,
                 steps :: Union{Nothing, Set{Step}}) :: Bool
    inc_w = g.inc[w]; inc_r = g.inc[r]
    #! [for] $ O(S) $
    for (l, set_x) in g.inc[x]
        (steps === nothing || l in steps) || continue
        set_w = get(inc_w, l, nothing); set_w === nothing && continue
        set_r = get(inc_r, l, nothing); set_r === nothing && continue
        #! [fixed] $ O(7) $
        any(q -> q in set_w && q in set_r, set_x) || return false
    end
    return true
end

# La regla de parejas con testigos buenos (TRIO_RULE).
function shares_every_step3(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId,
                            steps :: Union{Nothing, Set{Step}}) :: Bool
    inc_w = g.inc[w]
    #! [for] $ O(S) $
    for (step, set_x) in g.inc[x]
        set_w = get(inc_w, step, nothing)
        set_w === nothing && continue
        #! [fixed] $ O(7 * S * 7) $
        any(r -> r in set_w && trio_ok(g, x, w, r, steps), set_x) || return false
    end
    return true
end

function trio_steps() :: Union{Nothing, Set{Step}}
    TRIO_RULE[] == :clause || return nothing
    TRIO_STEPS[] === nothing && error("TRIO_RULE=:clause sin TRIO_STEPS (solo con el mapa bin)")
    return TRIO_STEPS[]
end

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
        trio = TRIO_RULE[] != :off
        steps = trio ? trio_steps() : nothing
        #! [for] $ O(|E|*S*7) $ (con TRIO_RULE, $ O(|E|*S*7*S*7) $)
        for e in values(og.edges)
            if !shares_every_step(og, e.a, e.b)
                @probe :pair_bad og e.a e.b
                push!(bad, (e.a, e.b))
            elseif trio && !shares_every_step3(og, e.a, e.b, steps)
                push!(bad, (e.a, e.b))
                TRIO_REMOVED[] += 1
            end
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

# Espejo de Lean `PairClosed` (lean/improves_bingo/AbsSatBingo/Model/ReviewClean.lean): cada arista comparte
# entrada en cada paso. Consulta para tests; tras make_review_owners! vale por construcción (el while de arriba
# llega a su punto fijo; en Lean es `pairClosed_review`, bajo `ReviewExitsClean`).
pair_closed(gpath :: GPath) :: Bool = all(e -> shares_every_step(gpath.og, e.a, e.b), values(gpath.og.edges))
