function up_filter_triangle_nodes!(gpath :: GPath, requires :: SetNodesId)
    if gpath.is_valid
        base_owners = Nothing
        
        for req_id in requires
            step_lit = req_id.step

            union_owners = Nothing

            # [for] O(N) - Max numer of nodes per step
            for node_id in PathCollectionLines.get_ids_step(gpath.table_lines, step_lit)
                node_step = PathCollectionLines.get_node(gpath.table_lines, node_id)

                # union of all owners of the nodes literal
                if union_owners == Nothing
                    union_owners = deepcopy(node_step.owners)
                else
                    PathDocumentOwners.union!(union_owners, node_step.owners)
                end
            end 

            if base_owners == Nothing
                base_owners = deepcopy(union_owners)
            else
                PathDocumentOwners.intersect!(base_owners, union_owners)
            end

            if !base_owners.valid 
                println("Detectada incompatibilidad!")
                gpath.is_valid = false
            end
        end

    end


end