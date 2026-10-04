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

    path0 = [node0_0_r, node1_1__0_0, node2_1__1_1, node3_0__2_1]


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

    path1 = [node0_1_r, node1_0__0_1, node2_1__1_0, node3_0__2_1]

    # Los owners ya no viven en el nodo: cada camino es una camarilla del grafo de owners.
    og = PathOwnersGraph.new()
    for _ in 0:3
        PathOwnersGraph.add_step!(og)
    end
    for node in unique(vcat(path0, path1))
        PathOwnersGraph.register!(og, node.id)
    end
    test_and_update_owners(og, path0)
    test_and_update_owners(og, path1)
    @test PathOwnersGraph.check_invariants(og)

    test_simulation_remove_0_0_r(deepcopy(og), path0, path1)
end


function test_simulation_remove_0_0_r(og, path0, path1)
    ## remove 0_0_r
    id_3_0__2_1 = Alias.new_path_id((step=3,index=0), (step=2,index=1))

    for node in vcat(path0, path1)
        @test PathOwnersGraph.is_valid_owners(og, node.id)
    end

    node0_0_r = first(path0)
    PathOwnersGraph.remove_node!(og, node0_0_r.id)
    @test PathOwnersGraph.check_invariants(og)

    # el camino 0 se queda sin nadie en el paso 0, salvo el nodo que comparte con el camino 1
    for node in path0[2:end]
        if node.id != id_3_0__2_1
            @test !PathOwnersGraph.is_valid_owners(og, node.id)
        end
    end

    for node in path1
        @test PathOwnersGraph.is_valid_owners(og, node.id)
    end
end

# Dentro de un camino: los enlaces ya son aristas (el UP las crea); el resto se añade aquí.
function test_and_update_owners(og, path_nodes)
    for node in path_nodes
        for node_check in path_nodes
            is_son = node_check.id in node.sons
            is_parent = node_check.id in node.parents
            (is_son || is_parent) && PathOwnersGraph.add_edge!(og, node.id, node_check.id)
        end
    end
    for node in path_nodes
        for node_check in path_nodes
            is_son = node_check.id in node.sons
            is_parent = node_check.id in node.parents
            is_myself = node_check.id == node.id
            if is_son || is_parent || is_myself
                @test PathOwnersGraph.has_edge(og, node.id, node_check.id)
            elseif !PathOwnersGraph.has_edge(og, node.id, node_check.id)
                PathOwnersGraph.add_edge!(og, node.id, node_check.id)
                @test PathOwnersGraph.has_edge(og, node_check.id, node.id)   # simétrica
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

    return node
end

test_simulate()
