# `prohibited` son las ventanas prohibidas del mapa (conjunto de PathNodeId); para el mapa clásico
# es vacío. Véase docs/plans/bin-map.md, Fase B.
function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                          prohibited :: Set{PathNodeId} = Set{PathNodeId}())
    # Etiquetas por fila (ROW_TAGS): la copia que sale del remitente es la pieza de su clave en su fila de cima.
    gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)

    filter!(gpath, requires)

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
    PathOwnersGraph.add_step!(gpath.og)
    if gpath.current_step == Step(0)
        add_root_node!(gpath, map_id_node, title)
    else
        parents_by_id = group_parents_by_shifted_id(gpath, map_id_node, prohibited)

        # La ventana prohibida (o un paso anterior vacío) no deja ningún candidato: el gpath muere.
        if isempty(parents_by_id)
            gpath.is_valid = false
            return
        end

        #! [for] $ O(7) $
        for (path_id_node, ids_parents) in parents_by_id
            create_node_from_parents!(gpath, path_id_node, ids_parents, title)
        end
    end
end

function add_root_node!(gpath :: GPath, map_id_node :: NodeId, title :: String)
    node = PathDocumentNode.new(Alias.root_path_id(map_id_node), title)
    PathCollectionLines.push_node!(gpath.table_lines, node)
    PathOwnersGraph.register!(gpath.og, node.id)
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
# Its edges go only to earlier steps, so the order in which the new row is created does not matter
# (no new node sees another one), as when every node was created before registering any.
function create_node_from_parents!(gpath :: GPath, path_id_node :: PathNodeId,
                                   ids_parents :: Vector{PathNodeId}, title :: String) :: PathDocNode
    node = PathDocumentNode.new(path_id_node, title)
    PathCollectionLines.push_node!(gpath.table_lines, node)
    #! [for] $ O(7*S*7*7) $
    PathOwnersGraph.create_from_parents!(gpath.og, node.id, ids_parents)

    #! [for] $ O(7) $
    for id_parent in ids_parents
        node_parent = PathCollectionLines.get_node(gpath.table_lines, id_parent)
        PathDocumentNode.link!(node_parent, node)
    end

    return node
end

# UP en sitio y reversible (rama optimizations-undo). up_in_place! aplica el UP a `gpath` anotando cómo
# deshacerlo; el llamador lee el resultado (is_valid, unir al destino, copiarlo) y llama a undo_up!, que
# devuelve `gpath` exactamente a su estado anterior. Sustituye a copiar el gpath en cada envío.
function up_in_place!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                      prohibited :: Set{PathNodeId} = Set{PathNodeId}())
    snap = (gpath.current_step, gpath.map_parent_id, gpath.review_owners, gpath.is_valid, gpath.og.nsteps, gpath.og.valid, gpath.og.krows)
    Undo.begin!()
    try
        do_up_filtering!(gpath, requires, map_id_node, title, prohibited)
    finally
        Undo.stop!()
    end
    return snap
end

function undo_up!(gpath :: GPath, snap)
    Undo.rollback!()
    gpath.current_step, gpath.map_parent_id, gpath.review_owners, gpath.is_valid = snap[1], snap[2], snap[3], snap[4]
    gpath.og.nsteps, gpath.og.valid, gpath.og.krows = snap[5], snap[6], snap[7]
    return gpath
end
