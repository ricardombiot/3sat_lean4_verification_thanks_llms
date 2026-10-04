
function test_create_node()
    node = MapDocumentNode.new((step=0,index=0),"0")

    @test node.id.step == 0
    @test node.id.index == 0
    @test node.title == "0"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test isempty(node.requires)
end

#=
0: x 0 1
1: !x 0 1
2: y 0 1
3: !y 0 1
4: w 0 1
5: !w 0 1

6: x=0, y=0, w=0 -> 000
... other gate 8 cases
=#
function test_create_node_gate()
    node = MapDocumentNode.new((step=6,index=0),"000")

    @test node.id.step == 6
    @test node.id.index == 0
    @test node.title == "000"
    @test isempty(node.parents)
    @test isempty(node.sons)
    @test isempty(node.requires)

    MapDocumentNode.add_parent!(node, (step=5,index=1))

    @test !isempty(node.parents)
    @test length(node.parents) == 1
    @test node.parents == Set([(step=5,index=1)])

    expected_list_sons = Array{NodeId,1}()
    for index in 0:7
        MapDocumentNode.add_son!(node, (step=7,index=index))
        push!(expected_list_sons, (step=7,index=index))
    end


    @test !isempty(node.sons)
    @test length(node.sons) == 8
    @test node.sons == Set(expected_list_sons)


    MapDocumentNode.add_require!(node, (step=0,index=0))
    MapDocumentNode.add_require!(node, (step=2,index=0))
    MapDocumentNode.add_require!(node, (step=4,index=0))

    @test !isempty(node.requires)
    @test length(node.requires) == 3
    @test node.requires == Set([(step=0,index=0), (step=2,index=0), (step=4,index=0)])
end

test_create_node()
test_create_node_gate()
