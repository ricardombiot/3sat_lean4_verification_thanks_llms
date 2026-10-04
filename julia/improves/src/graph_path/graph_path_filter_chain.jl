# regla de la cadena (19-sept-2026)
# ===========================
# Una relación a→z sobrevive solo si hay una cadena de hijos desde a hasta la cima
# en la que cada nodo es dueño común (en ambos sentidos) de a y de z.
# Los IDs de la cadena (nodo del mapa + padre) llevan a la cima de un lado.

function is_common_owner(node :: PathDocNode, node_a :: PathDocNode, node_z :: PathDocNode) :: Bool
    return PathDocumentOwners.is_owner(node.owners, node_a.id) &&
           PathDocumentOwners.is_owner(node.owners, node_z.id) &&
           PathDocumentOwners.is_owner(node_a.owners, node.id) &&
           PathDocumentOwners.is_owner(node_z.owners, node.id)
end

function is_linked(node_c :: PathDocNode, node_s :: PathDocNode) :: Bool
    return (node_s.id in node_c.sons) &&
           PathDocumentOwners.is_owner(node_c.owners, node_s.id) &&
           PathDocumentOwners.is_owner(node_s.owners, node_c.id)
end

# ¿Existe una cadena de hijos de dueños comunes de a y z, desde a hasta la cima?
# Se recorre de la cima hacia abajo: reach[c] = c puede subir hasta la cima.
function has_common_owner_chain(gpath :: GPath, node_a :: PathDocNode, node_z :: PathDocNode) :: Bool
    top = gpath.current_step - 1
    step_a = PathDocumentNode.get_step(node_a)
    reach = Dict{PathNodeId, Bool}()

    #! [for] $ O(S) $
    for step in top:-1:step_a
        #! [for] $ O(7*7) $
        for node_id in PathCollectionLines.get_ids_step(gpath.table_lines, step)
            node_c = PathCollectionLines.get_node(gpath.table_lines, node_id)
            is_start = node_id == node_a.id
            if !(is_start || is_common_owner(node_c, node_a, node_z))
                continue
            end
            if step == top
                reach[node_id] = true
            else
                ok = false
                #! [for] $ O(7*7) $
                for son_id in node_c.sons
                    if get(reach, son_id, false)
                        node_s = PathCollectionLines.get_node(gpath.table_lines, son_id)
                        if is_linked(node_c, node_s)
                            ok = true
                            break
                        end
                    end
                end
                reach[node_id] = ok
            end
        end
    end
    return get(reach, node_a.id, false)
end

function chain_consistence_filter!(gpath :: GPath)
    if gpath.is_valid
        #! [for] $ O(S) $
        for step in gpath.current_step-1:-1:0
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (node_a)
                if is_valid_node(gpath, node_a)
                    #! [for] $ O(S) $
                    for step_z in gpath.current_step-1:-1:0
                        # copia: se borra mientras se recorre
                        #! [for] $ O(7*7) $
                        for node_id_z in collect(node_a.owners.table[step_z])
                            node_id_z == node_a.id && continue
                            node_z = PathCollectionLines.get_node(gpath.table_lines, node_id_z)
                            if node_z != nothing && is_valid_node(gpath, node_z) && symmetric_entry(gpath, node_a, node_z)
                                if !has_common_owner_chain(gpath, node_a, node_z)
                                    PathDocumentNode.remove_owner!(node_a, node_id_z)
                                    PathDocumentNode.remove_owner!(node_z, node_a.id)
                                    println("[Chain filter] Step_a $(step) Step_z $(step_z) <-- ")
                                    gpath.review_owners = true
                                end
                            end
                        end
                    end
                end
                return remove_if_invalid_node!(gpath, node_a)
            end)
        end
    end
end