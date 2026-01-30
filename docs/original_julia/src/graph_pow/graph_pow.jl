module GraphPow
    #=
    GraphPath Basado en owners
    =#

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias

    mutable struct GPow
        lines_table :: Dict{Step, SetPathNodesId}
        owners_table :: Dict{PathNodeId, SetPathNodesId}
        owners_set :: SetPathNodesId
        nodes_to_remove :: SetPathNodesId
        current_step :: Step
        map_parent_id :: Union{NodeId,Nothing}
        review_owners :: Bool
        is_valid :: Bool

        kind_nodes_step :: Dict{Step, String}
    end



    function new() :: GPow
        lines_table = Dict{Step, SetPathNodesId}()
        owners_table = Dict{PathNodeId, SetPathNodesId}()
        owners_set = SetPathNodesId()
        nodes_to_remove = SetPathNodesId()
        current_step = Step(0)
        map_parent_id = nothing
        review_owners = false
        is_valid = true
        kind_nodes_step = Dict{Step, String}()

        GPow(lines_table, owners_table, owners_set, nodes_to_remove, current_step, map_parent_id,
                review_owners, is_valid, kind_nodes_step)
    end

    include("./graph_pow_up.jl")
    include("./graph_pow_join.jl")
    include("./graph_pow_abstract_node.jl")
    include("./graph_pow_filter.jl")

    include("./reader/path_pow_reader.jl")
    include("./reader/path_pow_exp_reader.jl")

end
