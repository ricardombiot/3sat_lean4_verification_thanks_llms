function test_new_gpath_up_root()
    gpath = GraphPath.new()

    @test gpath.map_parent_id == nothing
    @test gpath.current_step == Step(0)

    map_node_id = (step=0,index=1)
    GraphPath.do_up!(gpath, map_node_id,"x=1")

    @test gpath.map_parent_id == map_node_id
    @test gpath.current_step == Step(1)

    map_node_id_expected = Alias.new_path_id(map_node_id, nothing)
    @test GraphPath.is_alive(gpath, map_node_id_expected)
    node = PathCollectionLines.get_node(gpath.table_lines, map_node_id_expected)

    @test node.id.id.step == 0
    @test node.id.id.index == 1
    @test node.title == "x=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test GraphPath.is_owners_valid(gpath, node)
    # myself owner
    myself_id = node.id
    @test GraphPath.is_owner(gpath, node.id, myself_id)

    return gpath
end

function test_up_step_1(gpath)

    @test gpath.map_parent_id == (step=0,index=1)
    @test gpath.current_step == Step(1)

    map_node_id = (step=1,index=0)
    GraphPath.do_up!(gpath, map_node_id,"!x=0")

    @test gpath.map_parent_id == map_node_id
    @test gpath.current_step == Step(2)

    ## Comprobar los nodos
    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    id_1_0__0_1 = Alias.new_path_id((step=1,index=0), (step=0,index=1))

    @test GraphPath.is_alive(gpath, id_0_1_r)
    @test GraphPath.is_alive(gpath, id_1_0__0_1)

    node_0_1_r = PathCollectionLines.get_node(gpath.table_lines, id_0_1_r)
    node_1_0__0_1 = PathCollectionLines.get_node(gpath.table_lines, id_1_0__0_1)

    @test isempty(node_0_1_r.parents)
    @test !isempty(node_0_1_r.sons)
    @test node_0_1_r.sons == Set([id_1_0__0_1])

    @test !isempty(node_1_0__0_1.parents)
    @test node_1_0__0_1.parents == Set([id_0_1_r])
    @test isempty(node_1_0__0_1.sons)

    @test GraphPath.is_owner(gpath, node_0_1_r.id, id_0_1_r)
    @test GraphPath.is_owner(gpath, node_0_1_r.id, id_1_0__0_1)

    @test GraphPath.is_owner(gpath, node_1_0__0_1.id, id_0_1_r)
    @test GraphPath.is_owner(gpath, node_1_0__0_1.id, id_1_0__0_1)

    return gpath
end


function test_up_step_2(gpath)

    @test gpath.map_parent_id == (step=1,index=0)
    @test gpath.current_step == Step(2)

    map_node_id = (step=2,index=1)
    GraphPath.do_up!(gpath, map_node_id,"y=1")

    @test gpath.map_parent_id == map_node_id
    @test gpath.current_step == Step(3)

    ## Comprobar los nodos
    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    id_1_0__0_1 = Alias.new_path_id((step=1,index=0), (step=0,index=1))
    # ventana 3 (Alias.WINDOW): el id del paso 2 lleva padre y abuelo
    id_2_1__1_0 = Alias.PathNodeId((step=0,index=1), (step=1,index=0), (step=2,index=1))

    @test GraphPath.is_alive(gpath, id_0_1_r)
    @test GraphPath.is_alive(gpath, id_1_0__0_1)
    @test GraphPath.is_alive(gpath, id_2_1__1_0)

    node_0_1_r = PathCollectionLines.get_node(gpath.table_lines, id_0_1_r)
    node_1_0__0_1 = PathCollectionLines.get_node(gpath.table_lines, id_1_0__0_1)
    node_2_1__1_0 = PathCollectionLines.get_node(gpath.table_lines, id_2_1__1_0)

    @test isempty(node_0_1_r.parents)
    @test !isempty(node_0_1_r.sons)
    @test node_0_1_r.sons == Set([id_1_0__0_1])

    @test !isempty(node_1_0__0_1.parents)
    @test node_1_0__0_1.parents == Set([id_0_1_r])
    @test !isempty(node_1_0__0_1.sons)
    @test node_1_0__0_1.sons == Set([id_2_1__1_0])

    @test !isempty(node_2_1__1_0.parents)
    @test node_2_1__1_0.parents == Set([id_1_0__0_1])
    @test isempty(node_2_1__1_0.sons)

    @test GraphPath.is_owner(gpath, node_0_1_r.id, id_0_1_r)
    @test GraphPath.is_owner(gpath, node_0_1_r.id, id_1_0__0_1)
    @test GraphPath.is_owner(gpath, node_0_1_r.id, id_2_1__1_0)


    @test GraphPath.is_owner(gpath, node_1_0__0_1.id, id_0_1_r)
    @test GraphPath.is_owner(gpath, node_1_0__0_1.id, id_1_0__0_1)
    @test GraphPath.is_owner(gpath, node_1_0__0_1.id, id_2_1__1_0)

    @test GraphPath.is_owner(gpath, node_2_1__1_0.id, id_0_1_r)
    @test GraphPath.is_owner(gpath, node_2_1__1_0.id, id_1_0__0_1)
    @test GraphPath.is_owner(gpath, node_2_1__1_0.id, id_2_1__1_0)


    #==#
    return gpath
end

gpath = test_new_gpath_up_root()
gpath = test_up_step_1(gpath)
gpath = test_up_step_2(gpath)

# La tabla de owners en la visual sale del grafo (plan graph_owners, F3).
let node = PathCollectionLines.get_node(gpath.table_lines, Alias.new_path_id((step=0,index=1), nothing))
    txt = GraphPathVisual.draw_owners(gpath, node)
    @test occursin("0 :", txt) && occursin("2 :", txt) && !occursin("INVALID", txt)
end
