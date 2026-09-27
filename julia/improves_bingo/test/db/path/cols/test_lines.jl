function test_new_path_cols_lines()

    col_lines = PathCollectionLines.new()

    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    node = PathDocumentNode.new(id_0_1_r,"x=1")

    @test node.id.id.step == 0
    @test node.id.id.index == 1
    @test node.title == "x=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    PathCollectionLines.push_node!(col_lines, node)
    restore_node = PathCollectionLines.get_node(col_lines, node.id)
    @test restore_node == node

    col_nodes = PathCollectionLines.get_step(col_lines, Step(0))
    @test col_nodes.count == 1

    @test PathCollectionLines.get_ids_step(col_lines, Step(0)) == Set([node.id])

end


test_new_path_cols_lines()
