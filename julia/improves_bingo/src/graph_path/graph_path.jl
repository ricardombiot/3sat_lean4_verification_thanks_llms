module GraphPath
    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBDocuments.PathDocumentNode: PathDocNode
    using Main.AbsSat.DBDocuments.PathOwnersGraph: OwnersGraph
    using Main.AbsSat.DBCollections.PathCollectionNodes: PathColNodesLine
    using Main.AbsSat.DBCollections.PathCollectionLines: PathColLines


    using Main.AbsSat.Alias
    using Main.AbsSat.DBDocuments.PathDocumentNode
    using Main.AbsSat.DBDocuments.PathOwnersGraph
    using Main.AbsSat.DBCollections.PathCollectionNodes
    using Main.AbsSat.DBCollections.PathCollectionLines


    mutable struct GPath
        table_lines :: PathColLines
        og :: OwnersGraph                 # grafo de owners (plan docs/plans/graph_owners.md)
        current_step :: Step
        map_parent_id :: Union{NodeId,Nothing}
        review_owners :: Bool
        is_valid :: Bool
    end


    include("./graph_path_constructor.jl")
    include("./graph_path_owners.jl")
    include("./graph_path_up.jl")
    
    include("./graph_path_join.jl")
    include("./graph_path_filter.jl")
    include("./graph_path_filter_pair.jl")
    include("./graph_path_secpair.jl")
    include("./graph_path_edgeclique.jl")

    include("./reader/path_reader.jl")
    include("./reader/path_exp_reader.jl")

end
