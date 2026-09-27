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


    # Etiquetas de clave de todos los niveles (informe v197 §5, graph_path_keytags.jl). Por cada fila de claves ℓ, una
    # máscara uniforme (todas las entradas vienen de las mismas claves) o una por entrada (p, v) si un join la mezcló.
    const KeyMask = UInt64                      # bit i ⇔ nodo de mapa (ℓ, i)
    mutable struct KeyTagsAll
        uniform :: Dict{Step, KeyMask}
        mixed   :: Dict{Step, Dict{Tuple{PathNodeId, PathNodeId}, KeyMask}}
    end

    mutable struct GPath
        table_lines :: PathColLines
        owners :: PathDocOwners
        current_step :: Step
        map_parent_id :: Union{NodeId,Nothing}
        review_owners :: Bool
        is_valid :: Bool
        key_tags :: Union{KeyTagsAll, Nothing}  # `nothing` con KEYTAGS_MODE = :off
    end


    include("./graph_path_constructor.jl")
    include("./graph_path_up.jl")
    
    include("./graph_path_join.jl")
    include("./graph_path_filter.jl")
    include("./graph_path_filter_pair.jl")
    include("./graph_path_filter_agresive.jl")
    include("./graph_path_filter_triangle.jl")
    include("./graph_path_filter_chain.jl")
    include("./graph_path_keytags.jl")

    include("./reader/path_reader.jl")
    include("./reader/path_exp_reader.jl")

end
