function filter!(gpath :: GPath, requires :: SetNodesId)
    #! [for] $ O(3) $
    for map_node_id in requires
        filter_require!(gpath, map_node_id)
    end

    make_review_owners!(gpath)
end

# Contador de vueltas del review (solo para medir; no cambia nada).
const REVIEW_ROUNDS = Ref(0)

function make_review_owners!(gpath :: GPath)
    #! [recursive-if] $ O(S*7*7) $
    if gpath.is_valid && gpath.review_owners
        REVIEW_ROUNDS[] += 1
        #println("make Review_owners")
        gpath.review_owners = false
        clean_invalid_nodes!(gpath)
        if PAIR_MODE[] == :on
            pair_consistency_after_clean!(gpath)
        end
        
        review_owners_coherence_with_its_parents_sons!(gpath)

        #agressive_consistence_filter!(gpath)
        chain_consistence_filter!(gpath)

        if gpath.review_owners
            make_review_owners!(gpath)
        end
    end
end

# Interruptor de clean_invalid_nodes! (informe v181, §6):
#   :two_phase  — (por defecto) primero eliminar hasta que la global se estabilice, después un
#                 solo corte. Mismos veredictos, vueltas y estados finales que la secuencial en
#                 test_window y test_3sat, con un +1,3 % de tiempo en test_window.
#   :sequential — la de antes: nodo a nodo, cada tabla cortada con la global de ese momento.
const CLEAN_MODE = Ref(:two_phase)

function clean_invalid_nodes!(gpath :: GPath)
    if CLEAN_MODE[] == :two_phase
        clean_invalid_nodes_two_phase!(gpath)
    else
        clean_invalid_nodes_sequential!(gpath)
    end
end

function clean_invalid_nodes_sequential!(gpath :: GPath)
    # For every step  O(S) we have at worst O(7*7) nodes, then:
    #! [fn-iter] $ O(S*7*7) $
    PathCollectionLines.filter!(gpath.table_lines, function (map_node)
        PathDocumentOwners.intersect!(map_node.owners, gpath.owners)
        return remove_if_invalid_node!(gpath, map_node)
    end)
end

# cleanInvalid en dos fases (v181, §6), 24-sept-2026.
# Fase 1: se eliminan los nodos cuya tabla, cortada con la global ACTUAL, no es válida, sin tocar
#         todavía ninguna tabla; se repite hasta que no se elimina nada (eliminar un nodo puede dejar
#         a un vecino sin padres o sin hijos, o encoger la global).
# Fase 2: un solo corte de todas las tablas con la global FINAL. Así ninguna tabla guarda ids de
#         nodos eliminados y el resultado no depende del orden en que se recorren los nodos.
function clean_invalid_nodes_two_phase!(gpath :: GPath)
    #! [while] $ O(N) $ vueltas como mucho: cada vuelta que sigue ha eliminado al menos un nodo
    changed = true
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        #! [fn-iter] $ O(S*7*7) $
        PathCollectionLines.filter!(gpath.table_lines, function (path_node)
            #! [fixed] $ O(S*7) $ sin copiar la tabla: basta un id común por paso
            owners_ok = PathDocumentOwners.is_valid_intersect(path_node.owners, gpath.owners)
            if is_valid_node_by(gpath, path_node, owners_ok)
                return false
            else
                remove_node_owner!(gpath, path_node.id)
                clean_links!(gpath, path_node)
                gpath.review_owners = true
                changed = true
                return true
            end
        end)
    end

    #! [fn-iter] $ O(S*7*7) $
    PathCollectionLines.for_each(gpath.table_lines, function (path_node)
        if SYM_MODE[] == :on
            # Tras la purga todo nodo vivo está en la global, así que este corte solo quita ids
            # muertos y no hay espejo que escribir (plan A3, nota). Se comprueba con el contador.
            # (en un grafo inválido la purga se para antes: ahí puede haber vivos fuera de la global,
            # pero ese grafo se descarta)
            removed = PathDocumentOwners.intersect_removed!(path_node.owners, gpath.owners)
            if gpath.is_valid && gpath.table_lines.is_valid
                #! [for] $ O(S*7) $
                for w_id in removed
                    CLEAN_CUT_LIVE[] += PathCollectionLines.get_node(gpath.table_lines, w_id) !== nothing
                end
            end
        else
            PathDocumentOwners.intersect!(path_node.owners, gpath.owners)
        end
    end)
end
#! [fixed] $ O(S*7*7*S*7*7) $
#! [fixed] $ O(S*7*7*7*7) $

function remove_if_invalid_node!(gpath :: GPath, path_node :: PathDocNode) :: Bool
    is_valid = is_valid_node(gpath, path_node)
    if !is_valid
        remove_node_owner!(gpath, path_node.id)

        clean_links!(gpath, path_node)
        gpath.review_owners = true
        return true
    else
        return false
    end
end

function clean_links!(gpath :: GPath, path_node :: PathDocNode)
    #! [for] $ O(7*7) $
    for node_id_parent in path_node.parents
        node_parent = PathCollectionLines.get_node(gpath.table_lines, node_id_parent)
        PathDocumentNode.remove_son!(node_parent, path_node.id)
    end
    #! [for] $ O(7*7) $
    for node_id_son in path_node.sons
        node_son = PathCollectionLines.get_node(gpath.table_lines, node_id_son)
        PathDocumentNode.remove_parent!(node_son, path_node.id)
    end
end

# Review simétrico (docs/plans/review_simetrico.md, A2). Cuando el review quita w de la tabla de x
# afirma «ninguna solución pasa a la vez por x y por w»; la frase es simétrica, así que con :on se
# borra también el espejo: x sale de la tabla de w si w sigue vivo.
#   :on  — (por defecto desde el 24-sept-2026) las pasadas de padres y de hijos escriben el espejo.
#          compare_sym.jl: 80 instancias, mismos veredictos, estados finales y vueltas que :off,
#          +0,2 % de tiempo; la rama «asymmetric» del filtro agresivo deja de dispararse.
#   :off — la máquina de antes: el corte solo se escribe en la tabla de x.
const SYM_MODE = Ref(:on)

# Contadores (solo para medir; no cambian nada).
const MIRROR_REMOVED = Ref(0)   # entradas espejo borradas
const CLEAN_CUT_LIVE = Ref(0)   # ids de nodos VIVOS quitados por el corte de clean (debería ser 0)

# El corte de la tabla de x en una pasada, con espejo si SYM_MODE[] == :on.
function cut_owners!(gpath :: GPath, path_node :: PathDocNode, owners_cut :: PathDocOwners)
    if SYM_MODE[] == :on
        removed = PathDocumentOwners.intersect_removed!(path_node.owners, owners_cut)
        mirror_remove!(gpath, path_node.id, removed)
    else
        PathDocumentOwners.intersect!(path_node.owners, owners_cut)
    end
end

# x perdió estos owners: cada uno que siga vivo pierde a x. w no se valida aquí: si queda inválido
# lo elimina la propia pasada cuando lo procese o la purga de la vuelta siguiente.
function mirror_remove!(gpath :: GPath, x_id :: PathNodeId, removed :: Vector{PathNodeId})
    #! [for] $ O(S*7) $
    for w_id in removed
        node_w = PathCollectionLines.get_node(gpath.table_lines, w_id)
        if node_w !== nothing && PathDocumentOwners.is_owner(node_w.owners, x_id)
            PathDocumentNode.remove_owner!(node_w, x_id)
            MIRROR_REMOVED[] += 1
            gpath.review_owners = true
        end
    end
end

function review_owners_coherence_with_its_parents_sons!(gpath :: GPath)
    # hago la union de los owners de mis padres y la intersectiono conmigo
    review_owners_parents_sons!(gpath)

    # hago la union de los owners de mis hijos y la intersectiono conmigo
    review_owners_sons_parents!(gpath)
end

#=
Los owners deben ser coherentes con sus padres e hijos

# Top to down
# hago la union de los owners de mis padres y la intersectiono conmigo
=#
function review_owners_parents_sons!(gpath :: GPath)
    if gpath.is_valid && gpath.review_owners

        #! [for] $ O(S) $
        for step in 1:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                is_valid = is_valid_node(gpath, path_node)
                if is_valid
                    owners_union_parents = nothing
                    #! [for] $ O(7*7) $
                    for node_id_parent in path_node.parents
                        node_parent = PathCollectionLines.get_node(gpath.table_lines, node_id_parent)

                        if owners_union_parents == nothing
                            owners_union_parents = deepcopy(node_parent.owners)
                        else
                            PathDocumentOwners.union!(owners_union_parents, node_parent.owners)
                        end
                    end

                    cut_owners!(gpath, path_node, owners_union_parents)
                    return remove_if_invalid_node!(gpath, path_node)
                else
                    return remove_if_invalid_node!(gpath, path_node)
                end
            end)

            PathCollectionLines.check_if_valid_line!(gpath.table_lines, step)
            check_if_graph_valid!(gpath)
            if !gpath.is_valid
                break
            end
        end

    end
end


#=
Los owners deben ser coherentes con sus padres e hijos

down to top: union de owners de mis hijos intersect with me...

# Down to top
# hago la union de los owners de mis hijos y la intersectiono conmigo
=#
function review_owners_sons_parents!(gpath :: GPath)
    if gpath.is_valid && gpath.review_owners
        #! [for] $ O(S) $
        for step in gpath.current_step-2:-1:1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                is_valid = is_valid_node(gpath, path_node)

                if is_valid
                    owners_union_sons = nothing
                    #! [for] $ O(7*7) $
                    for node_id_son in path_node.sons
                        node_son = PathCollectionLines.get_node(gpath.table_lines, node_id_son)

                        if owners_union_sons == nothing
                            owners_union_sons = deepcopy(node_son.owners)
                        else
                            PathDocumentOwners.union!(owners_union_sons, node_son.owners)
                        end
                    end

                    cut_owners!(gpath, path_node, owners_union_sons)
                    return remove_if_invalid_node!(gpath, path_node)
                else
                    return remove_if_invalid_node!(gpath, path_node)
                end
            end)

            PathCollectionLines.check_if_valid_line!(gpath.table_lines, step)
            check_if_graph_valid!(gpath)
            if !gpath.is_valid
                break
            end
        end

    end
end


function filter_require!(gpath :: GPath, map_node_id_req :: NodeId)
    if gpath.is_valid
        step_selection = map_node_id_req.step
        nodes_ids = PathCollectionLines.get_ids_step(gpath.table_lines, step_selection)
        # Only literal steps, then:
        #! [for] $ O(2*2) $
        for node_id in nodes_ids
            is_required = node_id.id == map_node_id_req
            if !is_required
                remove_node_owner!(gpath, node_id)

                gpath.review_owners = true
            end
        end

        check_if_graph_valid!(gpath)
    end
end

function remove_node_owner!(gpath :: GPath, path_node_id :: PathNodeId)
    PathDocumentOwners.remove!(gpath.owners, path_node_id)
    check_if_graph_valid!(gpath)
end

function check_if_graph_valid!(gpath :: GPath)
    gpath.is_valid = PathDocumentOwners.is_valid(gpath.owners)
end


function is_valid_node(gpath :: GPath, path_node :: PathDocNode) :: Bool
    return is_valid_node_with_owners(gpath, path_node, path_node.owners)
end

# La validez de un nodo evaluada con una tabla de owners dada (la suya u otra), sin modificarlo.
function is_valid_node_with_owners(gpath :: GPath, path_node :: PathDocNode,
                                   owners :: PathDocOwners) :: Bool
    return is_valid_node_by(gpath, path_node, PathDocumentOwners.is_valid(owners))
end

# Las reglas de validez de un nodo, con la validez de su tabla ya calculada.
function is_valid_node_by(gpath :: GPath, path_node :: PathDocNode, is_owners_valid :: Bool) :: Bool
    is_root_node = PathDocumentNode.is_root(path_node)
    is_in_last_step = PathDocumentNode.get_step(path_node) == gpath.current_step-1
    have_parents = !isempty(path_node.parents)
    have_sons = !isempty(path_node.sons)


    if is_root_node
        if is_in_last_step
            #println("Filter ROOT by owners")
            return is_owners_valid
        else
            #println("Filter ROOT by owners OR sons $(gpath.current_step)")
            return is_owners_valid && have_sons
        end
    elseif is_in_last_step
        #println("Filter Hoja by owners, parents")
        return is_owners_valid && have_parents
    else
        #println("Filter by owners, parents or sons")
        return is_owners_valid && have_parents && have_sons
    end
end
