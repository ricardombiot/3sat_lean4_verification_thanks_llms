#DRAFT
# regla 2 (testigo enlazado)
# ===========================

# ¿Puede este nodo estar en el testigo de x→w? Dueño común, en ambos sentidos.
function allowed_in_witness(node :: PathDocNode, node_x :: PathDocNode, node_w :: PathDocNode) :: Bool
    return PathDocumentOwners.is_owner(node.owners, node_x.id) &&
           PathDocumentOwners.is_owner(node.owners, node_w.id) &&
           PathDocumentOwners.is_owner(node_x.owners, node.id) &&
           PathDocumentOwners.is_owner(node_w.owners, node.id)
end

# ¿Existe una cadena enlazada 0 → último paso, toda de dueños comunes de x y w?
# En el paso de x solo x es dueño de x, así que la cadena pasa por x (igual por w).
function has_linked_witness(gpath :: GPath, node_x :: PathDocNode, node_w :: PathDocNode) :: Bool
    frontier = Set{PathNodeId}()
    for id in PathCollectionLines.get_ids_step(gpath.table_lines, 0)
        node = PathCollectionLines.get_node(gpath.table_lines, id)
        if allowed_in_witness(node, node_x, node_w)
            push!(frontier, id)
        end
    end
    #! [for] $ O(S) $
    for step in 1:gpath.current_step-1
        next = Set{PathNodeId}()
        #! [for] $ O(7*7 * 7*7) $
        for id in frontier
            node = PathCollectionLines.get_node(gpath.table_lines, id)
            for son_id in node.sons
                son = PathCollectionLines.get_node(gpath.table_lines, son_id)
                if allowed_in_witness(son, node_x, node_w)
                    push!(next, son_id)
                end
            end
        end
        if isempty(next)
            return false
        end
        frontier = next
    end
    return !isempty(frontier)
end

function witness_consistence_filter!(gpath :: GPath)
    if gpath.is_valid
        for step in gpath.current_step-1:-1:1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
            PathCollectionNodes.filter!(col_nodes, function (node_x)
                if is_valid_node(gpath, node_x)
                    for step_w in step-1:-1:0                   # cada par una vez
                        for node_id_w in collect(node_x.owners.table[step_w])
                            node_w = PathCollectionLines.get_node(gpath.table_lines, node_id_w)
                            if is_valid_node(gpath, node_w) && symmetric_entry(gpath, node_x, node_w)
                                if !has_linked_witness(gpath, node_x, node_w)
                                    PathDocumentNode.remove_owner!(node_x, node_id_w)
                                    PathDocumentNode.remove_owner!(node_w, node_x.id)
                                    gpath.review_owners = true
                                end
                            end
                        end
                    end
                end
                return remove_if_invalid_node!(gpath, node_x)
            end)
        end
    end
end