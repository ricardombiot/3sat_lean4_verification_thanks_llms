function test_new_cols_nodes()

    col_nodes = MapCollectionNodes.new(Step(0))


    @test col_nodes.count == 0
    node = MapDocumentNode.new((step=0,index=0),"000")

    MapCollectionNodes.push_node!(col_nodes, node)

    restore_node = MapCollectionNodes.get_node(col_nodes, node.id)
    @test restore_node == node
    @test col_nodes.count == 1

    @test col_nodes.node_ids == Set([node.id])

end


test_new_cols_nodes()
