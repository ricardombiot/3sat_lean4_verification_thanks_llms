#=
             Root

0.0:R (x=0)    0.1:R (x=1)

1.1:0.0 (!x=1)  1.0:0.1 (!x=0)

2.1:1.1 (y=1)   2.1:1.0 (y=1)

        3.0:2.1 (!y=0)
=#
function test_simulate()

    node0_0_r = build_node0_0_r()
    node0_1_r = build_node0_1_r()

    node1_1__0_0 = build_node1_1__0_0()
    node1_0__0_1 = build_node1_0__0_1()

    node2_1__1_1 = build_node2_1__1_1()
    node2_1__1_0 = build_node2_1__1_0()

    node3_0__2_1 = build_node3_0__2_1()

    # path 0
    PathDocumentNode.link!(node0_0_r, node1_1__0_0)
    test_sons(node0_0_r, [node1_1__0_0])
    test_parents(node1_1__0_0, [node0_0_r])

    PathDocumentNode.link!(node1_1__0_0, node2_1__1_1)
    test_sons(node1_1__0_0, [node2_1__1_1])
    test_parents(node2_1__1_1, [node1_1__0_0])

    PathDocumentNode.link!(node2_1__1_1, node3_0__2_1)
    test_sons(node2_1__1_1, [node3_0__2_1])
    test_parents(node3_0__2_1, [node2_1__1_1])

    path0_owners = [node0_0_r, node1_1__0_0, node2_1__1_1, node3_0__2_1]
    test_and_update_owners(path0_owners)


    # path 1

    PathDocumentNode.link!(node0_1_r, node1_0__0_1)
    test_sons(node0_1_r, [node1_0__0_1])
    test_parents(node1_0__0_1, [node0_1_r])
    PathDocumentNode.link!(node1_0__0_1, node2_1__1_0)
    test_sons(node1_0__0_1, [node2_1__1_0])
    test_parents(node2_1__1_0, [node1_0__0_1])
    PathDocumentNode.link!(node2_1__1_0, node3_0__2_1)
    test_sons(node2_1__1_0, [node3_0__2_1])
    test_parents(node3_0__2_1, [node2_1__1_1, node2_1__1_0])

    path1_owners = [node0_1_r, node1_0__0_1, node2_1__1_0, node3_0__2_1]
    test_and_update_owners(path1_owners)

    test_simulation_remove_0_0_r(deepcopy(path0_owners), deepcopy(path1_owners))
end


function test_simulation_remove_0_0_r(path0_owners, path1_owners)
    ## remove 0_0_r
    graph_owners = PathDocumentOwners.new()
    # rebuild owners
    for node in path0_owners
        PathDocumentOwners.insert!(graph_owners, node.id)
    end
    for node in path1_owners
        PathDocumentOwners.insert!(graph_owners, node.id)
    end

    node0_0_r = first(path0_owners)
    PathDocumentOwners.remove!(graph_owners, node0_0_r.id)

    #txt = PathDocumentOwners.to_string(graph_owners)
    #println(txt)

    id_3_0__2_1 = Alias.new_path_id((step=3,index=0), (step=2,index=1))

    for node in path0_owners
        @test PathDocumentOwners.is_valid(node.owners)
        PathDocumentOwners.intersect!(node.owners, graph_owners)

        if node.id != id_3_0__2_1
            @test !PathDocumentOwners.is_valid(node.owners)
        end
    end

    for node in path1_owners
        @test PathDocumentOwners.is_valid(node.owners)
        PathDocumentOwners.intersect!(node.owners, graph_owners)
        @test PathDocumentOwners.is_valid(node.owners)
    end


end

function test_and_update_owners(path_node_owners)
    for node in path_node_owners
        for node_check in path_node_owners
            is_son = node_check.id in node.sons
            is_parent = node_check.id in node.parents
            is_myself = node_check.id == node.id
            if is_son || is_parent || is_myself
                @test PathDocumentOwners.is_owner(node.owners, node_check.id)
            else
                @test !PathDocumentOwners.is_owner(node.owners, node_check.id)
                PathDocumentOwners.insert!(node.owners, node_check.id)
                @test PathDocumentOwners.is_owner(node.owners, node_check.id)
            end
        end
    end
end

function test_sons(node, sons)
    @test length(node.sons) == length(sons)
    for node_son in sons
        @test node_son.id in node.sons
    end
end

function test_parents(node, parents)
    @test length(node.parents) == length(parents)
    for node_parent in parents
        @test node_parent.id in node.parents
    end
end


function build_node0_0_r()

    id_0_0_r = Alias.new_path_id((step=0,index=0), nothing)
    node = PathDocumentNode.new(id_0_0_r,"x=0")

    @test node.id.id.step == 0
    @test node.id.id.index == 0
    @test node.title == "x=0"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end

function build_node0_1_r()

    id_0_1_r = Alias.new_path_id((step=0,index=1), nothing)
    node = PathDocumentNode.new(id_0_1_r,"x=1")

    @test node.id.id.step == 0
    @test node.id.id.index == 1
    @test node.title == "x=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end


function build_node1_1__0_0()

    id_1_1__0_0 = Alias.new_path_id((step=1,index=1), (step=0,index=0))
    node = PathDocumentNode.new(id_1_1__0_0,"!x=1")

    @test node.id.id.step == 1
    @test node.id.id.index == 1
    @test node.title == "!x=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end


function build_node1_0__0_1()

    id_1_1__0_1 = Alias.new_path_id((step=1,index=0), (step=0,index=1))
    node = PathDocumentNode.new(id_1_1__0_1,"!x=0")

    @test node.id.id.step == 1
    @test node.id.id.index == 0
    @test node.title == "!x=0"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end

function build_node2_1__1_1()

    id_2_1__1_1 = Alias.new_path_id((step=2,index=1), (step=1,index=1))
    node = PathDocumentNode.new(id_2_1__1_1,"y=1")

    @test node.id.id.step == 2
    @test node.id.id.index == 1
    @test node.title == "y=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end

function build_node2_1__1_0()

    id_2_1__1_0 = Alias.new_path_id((step=2,index=1), (step=1,index=0))
    node = PathDocumentNode.new(id_2_1__1_0,"y=1")

    @test node.id.id.step == 2
    @test node.id.id.index == 1
    @test node.title == "y=1"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end

function build_node3_0__2_1()

    id_3_0__2_1 = Alias.new_path_id((step=3,index=0), (step=2,index=1))
    node = PathDocumentNode.new(id_3_0__2_1,"!y=0")

    @test node.id.id.step == 3
    @test node.id.id.index == 0
    @test node.title == "!y=0"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test PathDocumentOwners.is_valid(node.owners)

    return node
end

test_simulate()
