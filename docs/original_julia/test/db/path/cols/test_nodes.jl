function test_new_cols_path_nodes()

    col_nodes = PathCollectionNodes.new(Step(0))
    @test col_nodes.count == 0

    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    node = PathDocumentNode.new(id_0_1_r,"x=1")

    @test node.id.id.step == 0
    @test node.id.id.index == 1
    @test node.title == "x=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    PathCollectionNodes.push_node!(col_nodes, node)

    restore_node = PathCollectionNodes.get_node(col_nodes, node.id)
    @test restore_node == node
    @test col_nodes.count == 1

    @test col_nodes.node_ids == Set([node.id])

end


test_new_cols_path_nodes()
