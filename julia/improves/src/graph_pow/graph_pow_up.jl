function do_up_filtering!(gpath :: GPow, requires :: SetNodesId, map_id_node :: NodeId)
    filter!(gpath, requires)
    do_up!(gpath, map_id_node)
end

function do_up!(gpath :: GPow, map_id_node :: NodeId)
    if gpath.is_valid
        add_node_set_owners!(gpath, map_id_node)
        gpath.current_step += 1
        gpath.map_parent_id = map_id_node
    end
end

function add_node_set_owners!(gpath :: GPow, map_id_node :: NodeId)
    path_id_node = Alias.new_path_id(map_id_node, gpath.map_parent_id)

    gpath.lines_table[gpath.current_step] = SetPathNodesId([path_id_node])
    gpath.owners_table[path_id_node] = deepcopy(gpath.owners_set)

    add_as_owner_of_all!(gpath, path_id_node)
end


function add_as_owner_of_all!(gpath :: GPow, path_id_node :: PathNodeId)
    for (id, set_owners) in gpath.owners_table
        push!(set_owners, path_id_node)
    end
    push!(gpath.owners_set, path_id_node)
end
