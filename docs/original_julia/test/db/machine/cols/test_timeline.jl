function test_create_timeline()
    timeline = CollectionTimeline.new()

    CollectionTimeline.init_gpath_seed!(timeline,(step=0,index=0),"x=0")
    CollectionTimeline.init_gpath_seed!(timeline,(step=0,index=1),"x=1")

    @test CollectionTimeline.get_counter_graphs_step(timeline, Step(0)) == 2

    return timeline
end

function test_init_graph_x0(timeline)
    timeline_step = CollectionTimeline.get_step(timeline, Step(0))
    parent_id = (step=0,index=0)
    map_node_id_expected = Alias.new_path_id(parent_id, nothing)

    gpath_x0 = CollectionTimelineStep.get_gpath!(timeline_step, parent_id)

    @test gpath_x0 != nothing
    @test gpath_x0.map_parent_id == parent_id

    node = PathCollectionLines.get_node(gpath_x0.table_lines, map_node_id_expected)

    @test node.id.id.step == 0
    @test node.id.id.index == 0
    @test node.id.parent_id == nothing
    @test node.title == "x=0"
    @test isempty(node.parents)
    @test isempty(node.sons)
end

function test_init_graph_x1(timeline)
    timeline_step = CollectionTimeline.get_step(timeline, Step(0))
    parent_id = (step=0,index=1)
    map_node_id_expected = Alias.new_path_id(parent_id, nothing)
    gpath_x1 = CollectionTimelineStep.get_gpath!(timeline_step, parent_id)

    @test gpath_x1 != nothing
    @test gpath_x1.map_parent_id == parent_id

    node = PathCollectionLines.get_node(gpath_x1.table_lines, map_node_id_expected)

    @test node.id.id.step == 0
    @test node.id.id.index == 1
    @test node.id.parent_id == nothing
    @test node.title == "x=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
end

timeline = test_create_timeline()
test_init_graph_x0(timeline)
test_init_graph_x1(timeline)
