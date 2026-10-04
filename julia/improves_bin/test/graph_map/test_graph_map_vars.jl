function test_add_var()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    GraphMap.add_var!(gmap, "y")

    col_lines = gmap.table_lines
    test_step0(col_lines)
    test_step1(col_lines)
    test_step2(col_lines)
    test_step3(col_lines)

end

function test_step0(col_lines)
    node_x0 = MapCollectionLines.get_node(col_lines, (step=0, index=0))

    @test node_x0.title == "x=0"
    @test isempty(node_x0.parents)
    @test !isempty(node_x0.sons)
    @test node_x0.sons == Set([(step=1, index=1)])

    node_x1 = MapCollectionLines.get_node(col_lines, (step=0, index=1))

    @test node_x1.title == "x=1"
    @test isempty(node_x1.parents)
    @test !isempty(node_x1.sons)
    @test node_x1.sons == Set([(step=1, index=0)])
end

function test_step1(col_lines)
    node_x0_neg = MapCollectionLines.get_node(col_lines, (step=1, index=0))

    @test node_x0_neg.title == "!x=0"
    @test ! isempty(node_x0_neg.parents)
    @test node_x0_neg.parents == Set([(step=0, index=1)])
    @test ! isempty(node_x0_neg.sons)
    @test node_x0_neg.sons == Set([(step=2, index=0),(step=2, index=1)])

    node_x1_neg = MapCollectionLines.get_node(col_lines, (step=1, index=1))

    @test node_x1_neg.title == "!x=1"
    @test ! isempty(node_x1_neg.parents)
    @test node_x1_neg.parents == Set([(step=0, index=0)])
    @test ! isempty(node_x1_neg.sons)
    @test node_x1_neg.sons == Set([(step=2, index=0),(step=2, index=1)])
end

function test_step2(col_lines)
    node_y0 = MapCollectionLines.get_node(col_lines, (step=2, index=0))

    @test node_y0.title == "y=0"
    @test ! isempty(node_y0.parents)
    @test node_y0.parents == Set([(step=1, index=0),(step=1, index=1)])
    @test ! isempty(node_y0.sons)
    @test node_y0.sons == Set([(step=3, index=1)])

    node_y1 = MapCollectionLines.get_node(col_lines, (step=2, index=1))

    @test node_y1.title == "y=1"
    @test ! isempty(node_y1.parents)
    @test node_y1.parents == Set([(step=1, index=0),(step=1, index=1)])
    @test ! isempty(node_y1.sons)
    @test node_y1.sons == Set([(step=3, index=0)])
end

function test_step3(col_lines)
    node_y0_neg = MapCollectionLines.get_node(col_lines, (step=3, index=0))

    @test node_y0_neg.title == "!y=0"
    @test ! isempty(node_y0_neg.parents)
    @test node_y0_neg.parents == Set([(step=2, index=1)])
    @test isempty(node_y0_neg.sons)

    node_y1_neg = MapCollectionLines.get_node(col_lines, (step=3, index=1))

    @test node_y1_neg.title == "!y=1"
    @test ! isempty(node_y1_neg.parents)
    @test node_y1_neg.parents == Set([(step=2, index=0)])
    @test isempty(node_y1_neg.sons)
end

test_add_var()
