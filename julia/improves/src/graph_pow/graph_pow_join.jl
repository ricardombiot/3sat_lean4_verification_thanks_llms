function do_join!(gpath :: GPow, gpath_inmutable :: GPow)
    if is_valid_join(gpath, gpath_inmutable)
        gpath_inmutable = deepcopy(gpath_inmutable)

        Base.union!(gpath.owners_set, gpath_inmutable.owners_set)
        for path_id_node in gpath.owners_set
            step = path_id_node.id.step
            Base.push!(gpath.lines_table[step], path_id_node)

            set_owners_a = get_node_set_owners(gpath, path_id_node)
            set_owners_b = get_node_set_owners(gpath_inmutable, path_id_node)

            if set_owners_a == nothing
                gpath.owners_table[path_id_node] = deepcopy(set_owners_b)
            elseif set_owners_b != nothing
                Base.union!(set_owners_a, set_owners_b)
            end
        end
    end
end



function is_valid_join(gpath :: GPow, gpath_inmutable :: GPow) :: Bool
    eq_map_parent_id = gpath.map_parent_id == gpath_inmutable.map_parent_id
    eq_current_step = gpath.current_step == gpath_inmutable.current_step
    both_valids = gpath.is_valid && gpath_inmutable.is_valid

    return eq_map_parent_id && eq_current_step && both_valids
end
