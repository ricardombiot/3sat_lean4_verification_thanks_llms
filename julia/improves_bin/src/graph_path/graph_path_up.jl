# `prohibited` son las ventanas prohibidas del mapa (conjunto de PathNodeId); para el mapa clásico
# es vacío. Véase docs/plans/bin-map.md, Fase B.
function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                          prohibited :: Set{PathNodeId} = Set{PathNodeId}())

    filter!(gpath, requires)
    #up_filter_triangle_nodes!(gpath, requires)

    do_up!(gpath, map_id_node, title, prohibited)
end

function do_up!(gpath :: GPath, map_id_node :: NodeId, title :: String,
                prohibited :: Set{PathNodeId} = Set{PathNodeId}())
    if gpath.is_valid
        add_row!(gpath, map_id_node, title, prohibited)
        # add_row! puede invalidar el gpath (p. ej. la ventana prohibida no deja ningún candidato).
        if gpath.is_valid
            gpath.current_step += 1
            gpath.map_parent_id = map_id_node
            # Si se saltó una ventana prohibida, algún padre se quedó sin hijo: el UP lo poda aquí,
            # para que el gpath salga del UP revisado (review_owners = false, sin nodos muertos bajo
            # la cima), como en el mapa clásico. Va después de avanzar el paso: la fila nueva es la
            # cima y no necesita hijos.
            make_review_owners!(gpath)
        end
    end
end

#=
The new row has one node per identifier that the window shift gives to the nodes of the last row:
(gparent, parent, last) -> (parent, last, id)
Nodes of the last row that share `parent` shift to the same identifier, so they are merged
into one node with several parents.
=#
function add_row!(gpath :: GPath, map_id_node :: NodeId, title :: String,
                  prohibited :: Set{PathNodeId} = Set{PathNodeId}())
    if gpath.current_step == Step(0)
        add_root_node!(gpath, map_id_node, title)
    else
        parents_by_id = group_parents_by_shifted_id(gpath, map_id_node, prohibited)

        # La ventana prohibida (o un paso anterior vacío) no deja ningún candidato: el gpath muere.
        if isempty(parents_by_id)
            gpath.is_valid = false
            return
        end

        # First create every node, then register them: no new node can be seen by another one.
        new_nodes = PathDocNode[]
        #! [for] $ O(7) $
        for (path_id_node, ids_parents) in parents_by_id
            push!(new_nodes, create_node_from_parents!(gpath, path_id_node, ids_parents, title))
        end

        #! [for] $ O(7) $
        for node in new_nodes
            register_node!(gpath, node)
        end
    end
end

function add_root_node!(gpath :: GPath, map_id_node :: NodeId, title :: String)
    node = PathDocumentNode.new(Alias.root_path_id(map_id_node), title)
    register_node!(gpath, node)
end

function group_parents_by_shifted_id(gpath :: GPath, map_id_node :: NodeId,
                                     prohibited :: Set{PathNodeId} = Set{PathNodeId}()) :: Dict{PathNodeId, Vector{PathNodeId}}
    parents_by_id = Dict{PathNodeId, Vector{PathNodeId}}()
    last_step = gpath.current_step-1

    #! [for] $ O(7*7*7) $
    for id_last in PathCollectionLines.get_ids_step(gpath.table_lines, last_step)
        path_id_node = Alias.shift_path_id(id_last, map_id_node)
        # La ventana prohibida no se crea: (L1=0, L2=0, L3=0) no existe. Marcar para re-revisar:
        # el padre que solo tenía este candidato se queda sin hijo y debe ser podado.
        if path_id_node in prohibited
            gpath.review_owners = true
            continue
        end
        ids_parents = get!(parents_by_id, path_id_node, PathNodeId[])
        push!(ids_parents, id_last)
    end

    return parents_by_id
end

# The owners of the new node are what its parents own (only what is still alive), and itself.
function create_node_from_parents!(gpath :: GPath, path_id_node :: PathNodeId,
                                   ids_parents :: Vector{PathNodeId}, title :: String) :: PathDocNode
    owners = nothing
    #! [for] $ O(7) $
    for id_parent in ids_parents
        node_parent = PathCollectionLines.get_node(gpath.table_lines, id_parent)
        if owners === nothing
            owners = deepcopy(node_parent.owners)
        else
            PathDocumentOwners.union!(owners, node_parent.owners)
        end
    end
    PathDocumentOwners.intersect!(owners, gpath.owners)

    node = PathDocumentNode.new(path_id_node, title)
    node.owners = owners
    PathDocumentNode.add_owner!(node, node.id)

    #! [for] $ O(7) $
    for id_parent in ids_parents
        node_parent = PathCollectionLines.get_node(gpath.table_lines, id_parent)
        PathDocumentNode.link!(node_parent, node)
    end

    return node
end

function register_node!(gpath :: GPath, node :: PathDocNode)
    PathCollectionLines.push_node!(gpath.table_lines, node)
    PathDocumentOwners.insert!(gpath.owners, node.id)
    its_owners_are_owned_by_me!(gpath, node)
end

# Whoever owns the new node is owned by it (the ownership is symmetric from the start).
function its_owners_are_owned_by_me!(gpath :: GPath, node :: PathDocNode)
    #! [for] $ O(S*7*7) $
    for (step, set_owners_line) in node.owners.table
        for id_owner in set_owners_line
            id_owner == node.id && continue
            node_owner = PathCollectionLines.get_node(gpath.table_lines, id_owner)
            if node_owner != nothing
                PathDocumentNode.add_owner!(node_owner, node.id)
            end
        end
    end
end
