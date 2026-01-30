function filter!(gpath :: GPow, requires :: SetNodesId)
    gpath.nodes_to_remove = SetPathNodesId()
    for map_node_id in requires
        register_filter_nodes_by_require!(gpath, map_node_id)
    end

    if !isempty(gpath.nodes_to_remove)
        gpath.review_owners = true
        make_review_owners!(gpath)
    end
end

function make_review_owners!(gpath :: GPow)
    if gpath.is_valid && gpath.review_owners
        gpath.review_owners = false

        Base.setdiff!(gpath.owners_set, gpath.nodes_to_remove)
        gpath.nodes_to_remove = SetPathNodesId()

        clean_invalid_nodes!(gpath)
        review_owners_coherence_with_its_parents_sons!(gpath)


        if !isempty(gpath.nodes_to_remove)
            gpath.review_owners = true

            make_review_owners!(gpath)
        end
    end
end

function clean_invalid_nodes!(gpath :: GPow)
    for step in 0:gpath.current_step-1
        union_owners_step = SetPathNodesId()

        line_set = gpath.lines_table[step]
        for node_id in line_set
            if is_owner(gpath, node_id)
                set_owners_node = get_node_set_owners(gpath, node_id)
                Base.intersect!(set_owners_node, gpath.owners_set)
                Base.union!(union_owners_step, set_owners_node)
            else
                Base.delete!(line_set, node_id)
                Base.delete!(gpath.owners_table, node_id)
            end
        end

        if isempty(line_set)
            gpath.is_valid = false
        else
            review_chainowners!(gpath, union_owners_step)
        end
    end
end

function review_all_chainowners!(gpath :: GPow)
    for step in 0:gpath.current_step-1
        union_owners_step = SetPathNodesId()

        line_set = gpath.lines_table[step]
        for node_id in line_set
            if is_owner(gpath, node_id)
                set_owners_node = get_node_set_owners(gpath, node_id)
                Base.union!(union_owners_step, set_owners_node)
            end
        end

        review_chainowners!(gpath, union_owners_step)
    end
end


function review_owners_coherence_with_its_parents_sons!(gpath :: GPow)
    if gpath.is_valid
        review_owners_parents_sons!(gpath)
        review_owners_sons_parents!(gpath)
        review_all_chainowners!(gpath)
    end
end

#=
Los owners deben ser coherentes con sus padres e hijos
=#
function review_owners_parents_sons!(gpath :: GPow)
    if gpath.is_valid && gpath.review_owners
        # Top to down
        # hago la union de los owners de mis padres y la intersectiono conmigo
        for step in 1:gpath.current_step-1
            line_set = gpath.lines_table[step]
            for node_id in line_set
                if !is_pending_to_remove(gpath, node_id)
                    union_owners_parents = SetPathNodesId()
                    parents = get_node_parents_owners(gpath, node_id)

                    # no tiene padres y debería tenerlos.
                    if isempty(parents)
                        Base.push!(gpath.nodes_to_remove, node_id)
                    else
                        for node_id_parent in parents
                            set_owners_parent = get_node_set_owners(gpath, node_id_parent)
                            Base.union!(union_owners_parents, set_owners_parent)
                        end

                        set_node_owners = get_node_set_owners(gpath, node_id)
                        Base.intersect!(set_node_owners, set_owners_parent)
                        # podría ser invalido si en algun paso no tiene owners...
                        # we will use review_chainowners!
                    end
                end
            end
        end
    end

end

#=
Los owners deben ser coherentes con sus padres e hijos

down to top: union de owners de mis hijos intersect with me...
=#
function review_owners_sons_parents!(gpath :: GPow)
    if gpath.is_valid && gpath.review_owners
        # Top to down
        # hago la union de los owners de mis hijos y la intersectiono conmigo
        for step in gpath.current_step-2:-1:1
            line_set = gpath.lines_table[step]
            for node_id in line_set
                if !is_pending_to_remove(gpath, node_id)
                    union_owners_sons = SetPathNodesId()
                    sons = get_node_sons_owners(gpath, node_id)

                    # no tiene padres y debería tenerlos.
                    if isempty(sons)
                        Base.push!(gpath.nodes_to_remove, node_id)
                    else
                        for node_id_son in sons
                            set_owners_son = get_node_set_owners(gpath, node_id_son)
                            Base.union!(union_owners_sons, set_owners_son)
                        end

                        set_node_owners = get_node_set_owners(gpath, node_id)
                        Base.intersect!(set_node_owners, set_owners_sons)
                        # podría ser invalido si en algun paso no tiene owners...
                        # we will use review_chainowners!
                    end
                end
            end
        end
    end
end

function review_chainowners!(gpath :: GPow, union_owners_step :: SetPathNodesId)
    # Si uno de los nodos actuales no es owners de ningun de los
    # nodos validos de un paso, entonces su cadena de owners esta rota
    for node_id in gpath.owners_set
        is_node_chainowners_break = !(node_id in union_owners_step)
        if is_node_chainowners_break
            Base.push!(gpath.nodes_to_remove, node_id)
        end
    end
end

function register_filter_nodes_by_require!(gpath :: GPow, map_node_id_req :: NodeId)
    if gpath.is_valid
        step_selection = map_node_id_req.step
        nodes_ids = gpath.lines_table[step_selection]

        for node_id in nodes_ids
            is_required = node_id.id == map_node_id_req
            if !is_required
                Base.push!(gpath.nodes_to_remove, node_id)
            end
        end
    end
end
