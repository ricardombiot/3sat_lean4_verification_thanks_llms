function new() :: GPath
    table_lines = PathCollectionLines.new()
    og = PathOwnersGraph.new()
    current_step = Step(0)
    map_parent_id = nothing
    review_owners = false
    is_valid = true

    GPath(table_lines, og, current_step,
          map_parent_id, review_owners, is_valid)
end


# Copia por estructura, sin el IdDict del deepcopy genérico: es la copia de cada UP (send_to_destine!).
function copy_gpath(gpath :: GPath) :: GPath
    GPath(PathCollectionLines.copy_lines(gpath.table_lines), PathOwnersGraph.copy_graph(gpath.og),
          gpath.current_step, gpath.map_parent_id, gpath.review_owners, gpath.is_valid)
end

Base.deepcopy_internal(gpath :: GPath, stackdict :: IdDict) = get!(() -> copy_gpath(gpath), stackdict, gpath)
