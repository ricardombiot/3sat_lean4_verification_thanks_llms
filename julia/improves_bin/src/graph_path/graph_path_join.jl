function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
    if is_valid_join(gpath, gpath_inmutable)
        # Expensive operation...
        gpath_inmutable = deepcopy(gpath_inmutable)

        PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
        PathDocumentOwners.union!(gpath.owners, gpath_inmutable.owners)
    end
end


function is_valid_join(gpath :: GPath, gpath_inmutable :: GPath) :: Bool
    eq_map_parent_id = gpath.map_parent_id == gpath_inmutable.map_parent_id
    eq_current_step = gpath.current_step == gpath_inmutable.current_step
    both_valids = gpath.is_valid && gpath_inmutable.is_valid

    return eq_map_parent_id && eq_current_step && both_valids
end
