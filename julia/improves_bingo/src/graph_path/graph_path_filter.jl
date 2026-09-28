function filter!(gpath :: GPath, requires :: SetNodesId)
    #! [for] $ O(3) $
    for map_node_id in requires
        filter_require!(gpath, map_node_id)
    end

    make_review_owners!(gpath)
end

# Contador de vueltas del review (solo para medir; no cambia nada).
const REVIEW_ROUNDS = Ref(0)

# Comprobación de los invariantes del grafo de owners al final de cada review (plan
# docs/plans/graph_owners.md, F2). Solo para tests y diferenciales: con :on es lento.
const CHECK_OG = Ref(:off)

function make_review_owners!(gpath :: GPath)
    #! [recursive-if] $ O(S*7*7) $
    if gpath.is_valid && gpath.review_owners
        REVIEW_ROUNDS[] += 1
        gpath.review_owners = false
        clean_invalid_nodes!(gpath)
        if PAIR_MODE[] == :on
            pair_consistency_after_clean!(gpath)
        end
        LINK_MODE[] == :on && prune_stale_links!(gpath)

        review_owners_coherence_with_its_parents_sons!(gpath)

        LINK_MODE[] == :on && prune_stale_links!(gpath)

        if CHECK_OG[] == :on
            v = PathOwnersGraph.invariant_violation(gpath.og)
            v === nothing || error("grafo de owners: $v")
        end

        # regla de la estrella (graph_path_star.jl): solo con las demás reglas en su punto fijo
        if STAR_RULE[] == :on && !gpath.review_owners && gpath.is_valid && gpath.table_lines.is_valid
            star_rule!(gpath)
        end

        # regla de la etiqueta (graph_path_tags.jl): también con las demás reglas en su punto fijo
        if PathOwnersGraph.tags_on() && TAG_RULE[] == :on && !gpath.review_owners && gpath.is_valid && gpath.table_lines.is_valid
            tag_rule!(gpath)
        end

        if gpath.review_owners
            make_review_owners!(gpath)
        elseif FINAL_CHECK[] == :on && gpath.is_valid
            final_coherence_check!(gpath)
        end
    end
end

# Comprobación final (28-sept-2026; propuesta del informe v201, «closed» en lean/improves_bingo). Las pasadas de
# padres e hijos solo corren con review_owners: si la de hijos corta, el apoyo por padres de un paso superior
# puede quedar roto y el review salir sin repasarlo. Con :on, al salir se fuerza una vuelta de las dos pasadas (y
# la poda de enlaces); si cambian algo, el review sigue. Así el review solo sale cuando una vuelta completa con
# todas las reglas no cambia nada. Adoptado (informe v201 §5): :on por defecto; medido sin ningún cambio de
# veredicto, solución ni estado en 88 instancias × 2 mapas (test_3sat/probe_final_check.jl), +2–5 % de tiempo.
# Espejo de lean/improves_bingo `finalPass` en `reviewFuel`.
const FINAL_CHECK = Ref(:on)
const FINAL_CUTS = Ref(0)      # comprobaciones finales que cambiaron algo (solo para medir)
const FINAL_RUNS = Ref(0)      # comprobaciones finales hechas

function review_size(gpath :: GPath) :: Tuple{Int, Int, Int}
    nodes = 0; links = 0
    PathCollectionLines.for_each(gpath.table_lines, n -> (nodes += 1; links += length(n.parents) + length(n.sons)))
    return (length(gpath.og.edges), nodes, links)
end

function final_coherence_check!(gpath :: GPath)
    FINAL_RUNS[] += 1
    before = review_size(gpath)
    gpath.review_owners = true
    review_owners_coherence_with_its_parents_sons!(gpath)
    LINK_MODE[] == :on && gpath.is_valid && prune_stale_links!(gpath)
    if !gpath.is_valid || review_size(gpath) != before
        FINAL_CUTS[] += 1
        gpath.review_owners = true
        make_review_owners!(gpath)
    else
        gpath.review_owners = false
    end
end

# Enlaces caducados (26-sept-2026). Quitar un dueño (corte, parejas, regla de la cadena) puede dejar un
# enlace padre–hijo entre dos nodos que ya no se poseen: ninguna cadena lo puede usar. El modelo Lean los
# quita (`unlinkIncompatible`, `cutNode`: un enlace sobrevive si cada extremo posee al otro); con :on (por
# defecto) Julia hace lo mismo. Con el grafo de owners la posesión es simétrica: basta mirar la arista.
# Solo quita enlaces (no aristas); si quita alguno, pide otra vuelta de review (un nodo sin padres o sin
# hijos lo elimina la purga siguiente).
const LINK_MODE = Ref(:on)
const LINK_PRUNED = Ref(0)

function prune_stale_links!(gpath :: GPath)
    gpath.is_valid || return
    #! [fn-iter] $ O(S*7*7*7) $
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        for (links, back) in ((node.parents, :sons), (node.sons, :parents))
            #! [for] $ O(7) $
            for c_id in collect(links)
                node_c = PathCollectionLines.get_node(gpath.table_lines, c_id)
                if node_c === nothing || !PathOwnersGraph.has_edge(gpath.og, node.id, c_id)
                    delete!(links, c_id)
                    node_c !== nothing && delete!(getfield(node_c, back), node.id)
                    LINK_PRUNED[] += 1
                    gpath.review_owners = true
                end
            end
        end
    end)
end

# cleanInvalid (v181, §6). Se eliminan los nodos cuya tabla no es válida, y se repite hasta que no se
# elimina nada (eliminar un nodo puede dejar a un vecino sin padres, sin hijos, o con un paso sin
# owners). Con el grafo de owners ya no hay segunda fase: al eliminar un nodo se van sus aristas, así
# que ninguna tabla guarda ids de nodos muertos y el resultado no depende del orden del recorrido.
function clean_invalid_nodes!(gpath :: GPath)
    #! [while] $ O(N) $ vueltas como mucho: cada vuelta que sigue ha eliminado al menos un nodo
    changed = true
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        #! [fn-iter] $ O(S*7*7) $
        PathCollectionLines.filter!(gpath.table_lines, function (path_node)
            if is_valid_node(gpath, path_node)
                return false
            else
                remove_node_owner!(gpath, path_node.id; rule = :clean)
                clean_links!(gpath, path_node)
                gpath.review_owners = true
                changed = true
                return true
            end
        end)
    end
end

function remove_if_invalid_node!(gpath :: GPath, path_node :: PathDocNode) :: Bool
    is_valid = is_valid_node(gpath, path_node)
    if !is_valid
        remove_node_owner!(gpath, path_node.id; rule = :clean)

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

# El corte de la tabla de x en una pasada: se quita la arista (x,w) si ningún nodo de `supports`
# tiene la arista (·,w). Es el corte con la unión de sus tablas, sin copiarlas, y con el espejo incluido
# (la arista es una sola). Si quita alguna, pide otra vuelta de review.
function cut_owners!(gpath :: GPath, path_node :: PathDocNode, supports :: SetPathNodesId, rule :: Symbol)
    if PathOwnersGraph.cut_by_support!(gpath.og, path_node.id, supports; rule) > 0
        gpath.review_owners = true
    end
end

function review_owners_coherence_with_its_parents_sons!(gpath :: GPath)
    # corto mi tabla con la unión de las de mis padres
    review_owners_parents_sons!(gpath)

    # corto mi tabla con la unión de las de mis hijos
    review_owners_sons_parents!(gpath)
end

#=
Los owners deben ser coherentes con sus padres e hijos

# Top to down
# w sigue en mi tabla si algún padre mío tiene a w
=#
function review_owners_parents_sons!(gpath :: GPath)
    if gpath.is_valid && gpath.review_owners

        #! [for] $ O(S) $
        for step in 1:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                if is_valid_node(gpath, path_node)
                    #! [for] $ O(S*7*7*7) $
                    cut_owners!(gpath, path_node, path_node.parents, :parents)
                end
                return remove_if_invalid_node!(gpath, path_node)
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

# Down to top
# w sigue en mi tabla si algún hijo mío tiene a w
=#
function review_owners_sons_parents!(gpath :: GPath)
    if gpath.is_valid && gpath.review_owners
        #! [for] $ O(S) $
        for step in gpath.current_step-2:-1:0
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)

            #! [fn-iter] $ O(7*7) $
            PathCollectionNodes.filter!(col_nodes, function (path_node)
                if is_valid_node(gpath, path_node)
                    #! [for] $ O(S*7*7*7) $
                    cut_owners!(gpath, path_node, path_node.sons, :sons)
                end
                return remove_if_invalid_node!(gpath, path_node)
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
                remove_node_owner!(gpath, node_id; rule = :require)

                gpath.review_owners = true
            end
        end

        check_if_graph_valid!(gpath)
    end
end

# El nodo sale del grafo de owners con todas sus aristas. Su documento sigue en table_lines hasta que
# la purga lo encuentra (is_valid_node lo ve muerto).
function remove_node_owner!(gpath :: GPath, path_node_id :: PathNodeId; rule :: Symbol = :node)
    PathOwnersGraph.remove_node!(gpath.og, path_node_id; rule)
    check_if_graph_valid!(gpath)
end

function check_if_graph_valid!(gpath :: GPath)
    gpath.is_valid = gpath.og.valid
end

# La tabla de un nodo es válida si el nodo sigue en el grafo y tiene algún owner vivo en cada paso.
function is_owners_valid(gpath :: GPath, path_node :: PathDocNode) :: Bool
    return PathOwnersGraph.is_alive(gpath.og, path_node.id) &&
           PathOwnersGraph.is_valid_owners(gpath.og, path_node.id)
end

function is_valid_node(gpath :: GPath, path_node :: PathDocNode) :: Bool
    return is_valid_node_by(gpath, path_node, is_owners_valid(gpath, path_node))
end

# Las reglas de validez de un nodo, con la validez de su tabla ya calculada.
function is_valid_node_by(gpath :: GPath, path_node :: PathDocNode, is_owners_valid :: Bool) :: Bool
    is_root_node = PathDocumentNode.is_root(path_node)
    is_in_last_step = PathDocumentNode.get_step(path_node) == gpath.current_step-1
    have_parents = !isempty(path_node.parents)
    have_sons = !isempty(path_node.sons)


    if is_root_node
        if is_in_last_step
            return is_owners_valid
        else
            return is_owners_valid && have_sons
        end
    elseif is_in_last_step
        return is_owners_valid && have_parents
    else
        return is_owners_valid && have_parents && have_sons
    end
end
