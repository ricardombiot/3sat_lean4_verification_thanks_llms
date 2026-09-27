module GraphPath
    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBDocuments.PathDocumentNode: PathDocNode
    using Main.AbsSat.DBDocuments.PathDocumentOwners: PathDocOwners
    using Main.AbsSat.DBCollections.PathCollectionNodes: PathColNodesLine
    using Main.AbsSat.DBCollections.PathCollectionLines: PathColLines


    using Main.AbsSat.Alias
    using Main.AbsSat.DBDocuments.PathDocumentNode
    using Main.AbsSat.DBDocuments.PathDocumentOwners
    using Main.AbsSat.DBCollections.PathCollectionNodes
    using Main.AbsSat.DBCollections.PathCollectionLines


    # Etiqueta de clave de un nivel (informe v196 §3): de qué pieza viene cada entrada de las filas bajo la fila de
    # claves (la penúltima, current_step - 2). Solo vive una línea: el UP siguiente la sustituye.
    mutable struct KeyTags
        key_step :: Step                         # paso de las claves
        single   :: Union{NodeId, Nothing}       # pieza sin unir: toda entrada es de esta clave (etiqueta implícita)
        tags     :: Dict{Tuple{PathNodeId, PathNodeId}, SetNodesId}   # (p, v) => claves; solo tras un join
    end

    mutable struct GPath
        table_lines :: PathColLines
        owners :: PathDocOwners
        current_step :: Step
        map_parent_id :: Union{NodeId,Nothing}
        review_owners :: Bool
        is_valid :: Bool
        key_tags :: Union{KeyTags, Nothing}      # `nothing` en la raíz y con KEY_MODE = :off
    end


    include("./graph_path_constructor.jl")
    include("./graph_path_up.jl")
    
    include("./graph_path_join.jl")
    include("./graph_path_filter.jl")
    include("./graph_path_filter_pair.jl")
    include("./graph_path_filter_agresive.jl")
    include("./graph_path_filter_triangle.jl")
    include("./graph_path_filter_chain.jl")
    include("./graph_path_key.jl")

    include("./reader/path_reader.jl")
    include("./reader/path_exp_reader.jl")

end
