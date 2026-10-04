function test_new_cols_lines()

    col_lines = MapCollectionLines.new()

    node = MapDocumentNode.new((step=0,index=0),"000")
    MapCollectionLines.push_node!(col_lines, node)
    restore_node = MapCollectionLines.get_node(col_lines, node.id)
    @test restore_node == node

    col_nodes = MapCollectionLines.get_step(col_lines, Step(0))
    @test col_nodes.count == 1

    @test MapCollectionLines.get_ids_step(col_lines, Step(0)) == Set([node.id])

end


test_new_cols_lines()
