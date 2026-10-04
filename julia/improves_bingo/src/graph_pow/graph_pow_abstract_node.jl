function get_node_set_owners(gpath :: GPow, path_id_node :: PathNodeId) :: Union{Nothing, SetPathNodesId}
    if haskey(gpath.owners_table, path_id_node)
        return gpath.owners_table[path_id_node]
    else
        return nothing
    end
end


#=
KINDS:
"FUSION"
"ORS"
"LITERAL"
=#
function kind_node(gpath :: GPow, path_id_node :: PathNodeId) :: String
    step = path_id_node.id.step

    if haskey(gpath.kind_nodes_step, step)
        return gpath.kind_nodes_step[step]
    else
        return "LITERAL"
    end
end

function is_kind_literal(gpath :: GPow, path_id_node :: PathNodeId) :: Bool
    kind_node(gpath, path_id_node) == "LITERAL"
end

function register_step_of_fusion_nodes!(gpath :: GPow, step :: Step)
    gpath.kind_nodes_step[step] = "FUSION"
end

function register_step_of_fusion_ors!(gpath :: GPow, step :: Step)
    gpath.kind_nodes_step[step] = "ORS"
end

function is_owner(gpath :: GPow, path_id_node :: PathNodeId) :: Bool
    path_id_node in gpath.owners_set
end

function is_pending_to_remove(gpath :: GPow, path_id_node :: PathNodeId) :: Bool
    path_id_node in gpath.nodes_to_remove
end

function get_node_parents_owners(gpath :: GPow, path_id_node :: PathNodeId) :: SetPathNodesId
    set_parents = SetPathNodesId()
    step = path_id_node.id.step

    if step != Step(0)
        previous_step = step-1
        myowners = get_node_set_owners(gpath, path_id_node)
        nodes_previous_step = gpath.lines_table[previous_step]

        for node_id in myowners
            if node_id in nodes_previous_step
                Base.push!(set_parents, node_id)
            end
        end
    end

    return set_parents
end


function get_node_sons_owners(gpath :: GPow, path_id_node :: PathNodeId) :: SetPathNodesId
    set_sons = SetPathNodesId()
    step = path_id_node.id.step

    if step != gpath.current_step-1
        next_step = step+1
        myowners = get_node_set_owners(gpath, path_id_node)
        nodes_next_step = gpath.lines_table[next_step]

        for node_id in myowners
            if node_id in nodes_next_step
                Base.push!(set_sons, node_id)
            end
        end
    end

    return set_sons
end
