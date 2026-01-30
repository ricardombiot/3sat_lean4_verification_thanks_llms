function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String)
    filter!(gpath, requires)
    do_up!(gpath, map_id_node, title)
end

function do_up!(gpath :: GPath, map_id_node :: NodeId, title :: String)
    if gpath.is_valid
        add_node!(gpath, map_id_node, title)
        gpath.current_step += 1
        gpath.map_parent_id = map_id_node
    end
end

function add_node!(gpath :: GPath, map_id_node :: NodeId, title :: String)
    node = create_node!(gpath, map_id_node, title)
    link_with_parents!(gpath, node)
    PathDocumentNode.put_owners!(node, gpath.owners)
    PathCollectionLines.push_node!(gpath.table_lines, node)

    PathDocumentOwners.insert!(gpath.owners, node.id)
    all_previous_nodes_are_owners_of_me!(gpath, node)
end

function create_node!(gpath :: GPath, map_id_node :: NodeId, title :: String) :: PathDocNode
    path_id_node = Alias.new_path_id(map_id_node, gpath.map_parent_id)
    return PathDocumentNode.new(path_id_node,title)
end

function link_with_parents!(gpath :: GPath, node :: PathDocNode)
    if gpath.current_step > Step(0)
        last_step = gpath.current_step-1

        #! [fn-iter] $ O(S) $
        PathCollectionLines.for_each_on_step(gpath.table_lines, last_step, function (node_parent)
            PathDocumentNode.link!(node_parent, node)
        end)
    end
end

function all_previous_nodes_are_owners_of_me!(gpath :: GPath, node :: PathDocNode)
    #! [fn-iter] $ O(S*7*7) $
    PathCollectionLines.for_each(gpath.table_lines, function (node_previous)
        PathDocumentNode.add_owner!(node_previous, node.id)
    end)
end
