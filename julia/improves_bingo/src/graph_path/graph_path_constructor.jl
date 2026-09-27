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
