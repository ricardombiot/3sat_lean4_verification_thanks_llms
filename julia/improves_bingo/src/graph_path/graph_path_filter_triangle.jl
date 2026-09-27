# regla 19-sept-2026
# ===========================
function filter_triangle_nodes!(gpath :: GPath, requires :: SetNodesId)
    if gpath.is_valid
        base_owners = nothing

        for req_id in requires
            union_owners = nothing

            # Solo los nodos del literal pedido, no todos los del paso
            for node_id in PathCollectionLines.get_ids_step(gpath.table_lines, req_id.step)
                if node_id.id == req_id
                    node_step = PathCollectionLines.get_node(gpath.table_lines, node_id)
                    if union_owners === nothing
                        union_owners = deepcopy(node_step.owners)
                    else
                        PathDocumentOwners.union!(union_owners, node_step.owners)
                    end
                end
            end

            # Ningún nodo del literal pedido: el requisito no se puede cumplir
            if union_owners === nothing
                gpath.is_valid = false
                return
            end

            if base_owners === nothing
                base_owners = union_owners
            else
                PathDocumentOwners.intersect!(base_owners, union_owners)
            end

            # is_valid mira también los pasos vacíos, no solo el flag
            if !PathDocumentOwners.is_valid(base_owners)
                println("[Triangle filter] Detectada incompatibilidad!")
                gpath.is_valid = false
                return
            end
        end
    end
end