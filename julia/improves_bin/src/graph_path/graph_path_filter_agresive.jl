
# 14-sept-2026

# Veces que se dispara la rama «asymmetric» (solo para medir; con SYM_MODE :on debería quedar en 0).
const AGG_ASYM = Ref(0)
# Veces que se dispara la rama «inconsistente» (la que adelanta la regla de parejas; plan pair_mode A0).
const AGG_INCONS = Ref(0)

function agressive_consistence_filter!(gpath :: GPath)
    if gpath.is_valid 
        #! [for] $ O(S) $
        for step in gpath.current_step-1:-1:1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (node_x)
                is_valid = is_valid_node(gpath, node_x)
                if is_valid
                    #! [for] $ O(7*7) $
                    for step_w in gpath.current_step-1:-1:1
                        #! [for] $ O(7*7) $
                        for node_id_w in node_x.owners.table[step_w]
                            node_w = PathCollectionLines.get_node(gpath.table_lines, node_id_w)
                            
                            is_valid_w = is_valid_node(gpath, node_w)
                            if is_valid_w
                                if !symmetric_entry(gpath, node_x, node_w)
                                    PathDocumentNode.remove_owner!(node_x, node_id_w)
                                    AGG_ASYM[] += 1
                                    println("Apply Agressive: [Asymetric Detection] Step_x $(step) Step_w $(step_w) <-- ")
                                    gpath.review_owners = true
                                else
                                    # intersección de los owners 
                                    owners_copy = deepcopy(node_x.owners)
                                    PathDocumentOwners.intersect!(owners_copy, node_w.owners)

                                    if !PathDocumentOwners.is_valid(owners_copy)
                                        # No existe ningun camino en donde ambos sean compatibles, entonces dejan de ser owners.
                                        PathDocumentNode.remove_owner!(node_x, node_id_w)
                                        PathDocumentNode.remove_owner!(node_w, node_x.id)
                                        AGG_INCONS[] += 1
                                        is_valid_x = is_valid_node(gpath, node_x)
                                        is_valid_w = is_valid_node(gpath, node_w)
                                        println("Apply Agressive [Consistence] Step_x $(step) Step_w $(step_w) <-- ")
                                        gpath.review_owners = true
                                    end
                                end

                            end
                        end
                    end


                    return remove_if_invalid_node!(gpath, node_x)
                else
                    return remove_if_invalid_node!(gpath, node_x)
                end
            end)
        end
    end
end

function symmetric_entry(gpath :: GPath, path_node_x :: PathDocNode, 
                         path_node_w :: PathDocNode) :: Bool
    # ¿Está w en los owners de x Y está x en los owners de w?
    x_owns_w = PathDocumentOwners.is_owner(path_node_x.owners, path_node_w.id)
    w_owns_x = PathDocumentOwners.is_owner(path_node_w.owners, path_node_x.id)
    
    return x_owns_w && w_owns_x
end