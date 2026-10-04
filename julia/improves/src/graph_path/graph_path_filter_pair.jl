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
const PAIR_MODE = Ref(:off)

# Contadores (solo para medir; no cambian nada).
const PAIR_REMOVED = Ref(0)     # parejas deshechas (cada pareja mutua cuenta dos veces: (x,w) y (w,x))
const PAIR_ROUNDS  = Ref(0)     # vueltas regla + purga
const PAIR_MAXSTEP = Ref(0)     # parejas comparadas con max_step distinto (debería ser 0)

function pair_consistency_after_clean!(gpath :: GPath)
    changed = true
    #! [while] $ O(N*7) $ vueltas como mucho: cada vuelta que sigue ha deshecho al menos una pareja
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        PAIR_ROUNDS[] += 1

        # Fase 1: las parejas malas, contra el estado de ahora.
        bad = Tuple{PathNodeId, PathNodeId}[]
        #! [fn-iter] $ O(S*7*7) $
        PathCollectionLines.for_each(gpath.table_lines, function (node_x)
            #! [for] $ O(S) $
            for (_, ids_w) in node_x.owners.table
                #! [for] $ O(7*7) $
                for node_id_w in ids_w
                    node_id_w == node_x.id && continue
                    node_w = PathCollectionLines.get_node(gpath.table_lines, node_id_w)
                    node_w === nothing && continue      # id muerto: lo quita el corte de clean
                    PAIR_MAXSTEP[] += node_w.owners.max_step != node_x.owners.max_step
                    #! [fixed] $ O(S*7) $
                    if !PathDocumentOwners.shares_every_step(node_x.owners, node_w.owners)
                        push!(bad, (node_x.id, node_id_w))
                    end
                end
            end
        end)

        # Fase 2: se quitan todas, en las dos direcciones (quitar un id que ya no está es inocuo).
        #! [for] $ O(|bad|) $
        for (x_id, w_id) in bad
            node_x = PathCollectionLines.get_node(gpath.table_lines, x_id)
            node_w = PathCollectionLines.get_node(gpath.table_lines, w_id)
            node_x !== nothing && PathDocumentNode.remove_owner!(node_x, w_id)
            node_w !== nothing && PathDocumentNode.remove_owner!(node_w, x_id)
            PAIR_REMOVED[] += 1
            changed = true
        end

        if changed
            gpath.review_owners = true
            # purga + corte con la global final: deshacer una pareja puede dejar un paso vacío
            clean_invalid_nodes!(gpath)
        end
    end
end
