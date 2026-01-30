function filter!(gpath :: GPath, requires :: SetNodesId)
    #! [for] $ O(3) $
    for map_node_id in requires
        filter_require!(gpath, map_node_id)
    end

    make_review_owners!(gpath)
end

function make_review_owners!(gpath :: GPath)
    #! [recursive-if] $ O(S*7*7) $
    if gpath.is_valid && gpath.review_owners
        #println("make Review_owners")
        gpath.review_owners = false
        clean_invalid_nodes!(gpath)
        #review_owners_parents_sons!(gpath)
        review_owners_coherence_with_its_parents_sons!(gpath)
        ## Second time
        #println("Second time..")
        #clean_invalid_nodes!(gpath)
        #println("End Second time..")

        if gpath.review_owners
            make_review_owners!(gpath)
        end
    end
end

function clean_invalid_nodes!(gpath :: GPath)
    # For every step  O(S) we have at worst O(7*7) nodes, then:
    #! [fn-iter] $ O(S*7*7) $
    PathCollectionLines.filter!(gpath.table_lines, function (map_node)
        PathDocumentOwners.intersect!(map_node.owners, gpath.owners)
        return remove_if_invalid_node!(gpath, map_node)
    end)
end
#! [fixed] $ O(S*7*7*S*7*7) $
#! [fixed] $ O(S*7*7*7*7) $

function remove_if_invalid_node!(gpath :: GPath, path_node :: PathDocNode) :: Bool
    is_valid = is_valid_node(gpath, path_node)
    if !is_valid
        remove_node_owner!(gpath, path_node.id)

        clean_links!(gpath, path_node)
        gpath.review_owners = true
        return true
    else
        return false
    end
end

function clean_links!(gpath :: GPath, path_node :: PathDocNode)
    #! [for] $ O(7*7) $
    for node_id_parent in path_node.parents
        node_parent = PathCollectionLines.get_node(gpath.table_lines, node_id_parent)
        PathDocumentNode.remove_son!(node_parent, path_node.id)
    end
    #! [for] $ O(7*7) $
    for node_id_son in path_node.sons
        node_son = PathCollectionLines.get_node(gpath.table_lines, node_id_son)
        PathDocumentNode.remove_parent!(node_son, path_node.id)
    end
end

function review_owners_coherence_with_its_parents_sons!(gpath :: GPath)
    # hago la union de los owners de mis padres y la intersectiono conmigo
    review_owners_parents_sons!(gpath)

    # hago la union de los owners de mis hijos y la intersectiono conmigo
    review_owners_sons_parents!(gpath)
end

#=
Los owners deben ser coherentes con sus padres e hijos

# Top to down
# hago la union de los owners de mis padres y la intersectiono conmigo
=#
function review_owners_parents_sons!(gpath :: GPath)
    if gpath.is_valid && gpath.review_owners

        #! [for] $ O(S) $
        for step in 1:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                is_valid = is_valid_node(gpath, path_node)
                if is_valid
                    owners_union_parents = nothing
                    #! [for] $ O(7*7) $
                    for node_id_parent in path_node.parents
                        node_parent = PathCollectionLines.get_node(gpath.table_lines, node_id_parent)

                        if owners_union_parents == nothing
                            owners_union_parents = deepcopy(node_parent.owners)
                        else
                            PathDocumentOwners.union!(owners_union_parents, node_parent.owners)
                        end
                    end

                    PathDocumentOwners.intersect!(path_node.owners, owners_union_parents)
                    return remove_if_invalid_node!(gpath, path_node)
                else
                    return remove_if_invalid_node!(gpath, path_node)
                end
            end)

            PathCollectionLines.check_if_valid_line!(gpath.table_lines, step)
            check_if_graph_valid!(gpath)
            if !gpath.is_valid
                break
            end
        end

    end
end


#=
Los owners deben ser coherentes con sus padres e hijos

down to top: union de owners de mis hijos intersect with me...

# Down to top
# hago la union de los owners de mis hijos y la intersectiono conmigo
=#
function review_owners_sons_parents!(gpath :: GPath)
    if gpath.is_valid && gpath.review_owners
        #! [for] $ O(S) $
        for step in gpath.current_step-2:-1:1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                is_valid = is_valid_node(gpath, path_node)

                if is_valid
                    owners_union_sons = nothing
                    #! [for] $ O(7*7) $
                    for node_id_son in path_node.sons
                        node_son = PathCollectionLines.get_node(gpath.table_lines, node_id_son)

                        if owners_union_sons == nothing
                            owners_union_sons = deepcopy(node_son.owners)
                        else
                            PathDocumentOwners.union!(owners_union_sons, node_son.owners)
                        end
                    end

                    PathDocumentOwners.intersect!(path_node.owners, owners_union_sons)
                    return remove_if_invalid_node!(gpath, path_node)
                else
                    return remove_if_invalid_node!(gpath, path_node)
                end
            end)

            PathCollectionLines.check_if_valid_line!(gpath.table_lines, step)
            check_if_graph_valid!(gpath)
            if !gpath.is_valid
                break
            end
        end

    end
end

function filter_require!(gpath :: GPath, map_node_id_req :: NodeId)
    if gpath.is_valid
        step_selection = map_node_id_req.step
        nodes_ids = PathCollectionLines.get_ids_step(gpath.table_lines, step_selection)
        # Only literal steps, then:
        #! [for] $ O(2*2) $
        for node_id in nodes_ids
            is_required = node_id.id == map_node_id_req
            if !is_required
                remove_node_owner!(gpath, node_id)

                gpath.review_owners = true
            end
        end

        check_if_graph_valid!(gpath)
    end
end

function remove_node_owner!(gpath :: GPath, path_node_id :: PathNodeId)
    PathDocumentOwners.remove!(gpath.owners, path_node_id)
    check_if_graph_valid!(gpath)
end

function check_if_graph_valid!(gpath :: GPath)
    gpath.is_valid = PathDocumentOwners.is_valid(gpath.owners)
end


function is_valid_node(gpath :: GPath, path_node :: PathDocNode) :: Bool
    is_owners_valid = PathDocumentNode.is_valid(path_node)
    is_root_node = PathDocumentNode.is_root(path_node)
    is_in_last_step = PathDocumentNode.get_step(path_node) == gpath.current_step-1
    have_parents = !isempty(path_node.parents)
    have_sons = !isempty(path_node.sons)


    if is_root_node
        if is_in_last_step
            #println("Filter ROOT by owners")
            return is_owners_valid
        else
            #println("Filter ROOT by owners OR sons $(gpath.current_step)")
            return is_owners_valid && have_sons
        end
    elseif is_in_last_step
        #println("Filter Hoja by owners, parents")
        return is_owners_valid && have_parents
    else
        #println("Filter by owners, parents or sons")
        return is_owners_valid && have_parents && have_sons
    end
end
