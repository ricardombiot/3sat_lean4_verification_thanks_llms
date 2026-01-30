function test_gpow()
    gpath = GraphPow.new()

    @test gpath.map_parent_id == nothing
    @test gpath.current_step == Step(0)

    map_node_id = (step=0,index=1)
    GraphPow.do_up!(gpath, map_node_id)

    @test gpath.map_parent_id == map_node_id
    @test gpath.current_step == Step(1)

    map_node_id_expected = Alias.new_path_id(map_node_id, nothing)
    @test gpath.owners_set == Set([map_node_id_expected])
    sons = GraphPow.get_node_sons_owners(gpath, map_node_id_expected)
    @test isempty(sons)
    parents = GraphPow.get_node_parents_owners(gpath, map_node_id_expected)
    @test isempty(parents)

    return gpath
end

function test_gpow_up_step_1(gpath)

    @test gpath.map_parent_id == (step=0,index=1)
    @test gpath.current_step == Step(1)

    map_node_id = (step=1,index=0)
    GraphPow.do_up!(gpath, map_node_id)

    @test gpath.map_parent_id == map_node_id
    @test gpath.current_step == Step(2)

    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    id_1_0__0_1 = Alias.new_path_id((step=1,index=0), (step=0,index=1))
    @test gpath.owners_set == Set([id_0_1_r, id_1_0__0_1])

    # Testing id_0_1_r
    parents = GraphPow.get_node_parents_owners(gpath, id_0_1_r)
    @test isempty(parents)
    sons = GraphPow.get_node_sons_owners(gpath, id_0_1_r)
    @test !isempty(sons)
    @test sons == Set([id_1_0__0_1])

    # Testing id_1_0__0_1
    parents = GraphPow.get_node_parents_owners(gpath, id_1_0__0_1)
    @test !isempty(parents)
    @test parents == Set([id_0_1_r])
    sons = GraphPow.get_node_sons_owners(gpath, id_1_0__0_1)
    @test isempty(sons)


    return gpath
end


function test_gpow_up_step_2(gpath)

    @test gpath.map_parent_id == (step=1,index=0)
    @test gpath.current_step == Step(2)

    map_node_id = (step=2,index=1)
    GraphPow.do_up!(gpath, map_node_id)

    @test gpath.map_parent_id == map_node_id
    @test gpath.current_step == Step(3)

    ## Comprobar los nodos
    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    id_1_0__0_1 = Alias.new_path_id((step=1,index=0), (step=0,index=1))
    id_2_1__1_0 = Alias.new_path_id((step=2,index=1), (step=1,index=0))
    set_all_nodes = Set([id_0_1_r, id_1_0__0_1,id_2_1__1_0])
    @test gpath.owners_set == set_all_nodes


    # Testing id_0_1_r
    parents = GraphPow.get_node_parents_owners(gpath, id_0_1_r)
    @test isempty(parents)
    sons = GraphPow.get_node_sons_owners(gpath, id_0_1_r)
    @test !isempty(sons)
    @test sons == Set([id_1_0__0_1])
    owners = GraphPow.get_node_set_owners(gpath, id_0_1_r)
    @test owners == set_all_nodes

    # Testing id_1_0__0_1
    parents = GraphPow.get_node_parents_owners(gpath, id_1_0__0_1)
    @test !isempty(parents)
    @test parents == Set([id_0_1_r])
    sons = GraphPow.get_node_sons_owners(gpath, id_1_0__0_1)
    @test !isempty(sons)
    @test sons == Set([id_2_1__1_0])
    owners = GraphPow.get_node_set_owners(gpath, id_1_0__0_1)
    @test owners == set_all_nodes

    # Testing id_2_1__1_0
    parents = GraphPow.get_node_parents_owners(gpath, id_2_1__1_0)
    @test !isempty(parents)
    @test parents == Set([id_1_0__0_1])
    sons = GraphPow.get_node_sons_owners(gpath, id_2_1__1_0)
    @test isempty(sons)
    owners = GraphPow.get_node_set_owners(gpath, id_2_1__1_0)
    @test owners == set_all_nodes



    #diagram = GraphPowVisual.build(gpath)
    #GraphPowVisual.to_png(diagram, "gpath_pow_example")

    return gpath
end

gpath = test_gpow()
gpath = test_gpow_up_step_1(gpath)
gpath = test_gpow_up_step_2(gpath)
