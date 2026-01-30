module PathDocumentOwners

    using Main.AbsSat.Alias: Step, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias


    mutable struct PathDocOwners
        table :: Dict{Step, SetPathNodesId}
        max_step :: Step
        empty_steps :: Set{Step}
        valid :: Bool
    end

    function new() :: PathDocOwners
        table = Dict{Step, SetPathNodesId}()
        max_step = Step(-1)
        empty_steps = Set{Step}()
        valid = true
        PathDocOwners(table, max_step, empty_steps, valid)
    end

    function is_valid(owners :: PathDocOwners) :: Bool
        return owners.valid && isempty(owners.empty_steps)
    end

    function have(owners :: PathDocOwners, step :: Step) :: Bool
        return haskey(owners.table, step)
    end

    function get(owners :: PathDocOwners, step :: Step) :: Union{SetPathNodesId,Nothing}
        if have(owners, step)
            return owners.table[step]
        else
            return nothing
        end
    end


    function push_derive!(owners :: PathDocOwners, step :: Step, set_owners_line :: SetPathNodesId)
        set_owners_line_derive = deepcopy(set_owners_line)
        owners.table[step] = set_owners_line_derive
    end

    function create_owners_line!(owners :: PathDocOwners, step :: Step)
        owners.table[step] = SetPathNodesId()

        if step > owners.max_step
            owners.max_step = step
        end
    end

    function insert_secure!(owners :: PathDocOwners, node_id :: PathNodeId)
        if have(owners, node_id.id.step)
            set_owners_line = owners.table[node_id.id.step]
            push!(set_owners_line, node_id)
        end
    end

    function insert!(owners :: PathDocOwners, node_id :: PathNodeId)
        if !have(owners, node_id.id.step)
            create_owners_line!(owners, node_id.id.step)
        end

        insert_secure!(owners, node_id)
    end

    function remove!(owners :: PathDocOwners, node_id :: PathNodeId)
        if have(owners, node_id.id.step)
            set_owners_line = owners.table[node_id.id.step]
            delete!(set_owners_line, node_id)

            check_if_isempty!(owners, node_id.id.step)
        end
    end

    function is_owner(owners :: PathDocOwners, node_id :: PathNodeId) :: Bool
        if have(owners, node_id.id.step)
            set_owners_line = owners.table[node_id.id.step]
            return node_id in set_owners_line
        else
            return false
        end
    end

    function union!(owners_a :: PathDocOwners, owners_b :: PathDocOwners)
        max_step = owners_a.max_step

        if max_step < owners_b.max_step
            max_step = owners_b.max_step
        end

        #! [for] $ O(S) $
        for step in 0:max_step
            both_have_it = have(owners_a, step) && have(owners_b, step)
            if both_have_it
                set_owners_line_a = get(owners_a, step)
                set_owners_line_b = get(owners_b, step)

                #! [fixed] $ O(S*7*7) $
                Base.union!(set_owners_line_a, set_owners_line_b)
            else
                if have(owners_b, step)
                    set_owners_line_b = get(owners_b, step)
                    #! [fixed] $ O(S*7) $
                    push_derive!(owners_a, step, set_owners_line_b)
                end
            end
        end
    end

    function intersect!(owners_a :: PathDocOwners, owners_b :: PathDocOwners)
        if owners_b.max_step > owners_a.max_step
            owners_a.valid = false
        else
            #! [for] $ O(S) $
            for step in 0:owners_a.max_step
                both_have_it = have(owners_a, step) && have(owners_b, step)
                if both_have_it
                    set_owners_line_a = get(owners_a, step)
                    set_owners_line_b = get(owners_b, step)

                    #! [fixed] $ O(S*7*7) $
                    for owner_id in set_owners_line_a
                        is_owner = owner_id in set_owners_line_b
                        if !is_owner
                            delete!(set_owners_line_a, owner_id)
                            #count = length(set_owners_line_a)
                            #println("Delete Owner... $count")
                        end
                    end

                    #Base.intersect!(set_owners_line_a, set_owners_line_b)

                    check_if_isempty!(owners_a, step)
                end

                #if !is_valid(owners)
                #    return;
                #end
            end
        end
    end



    function check_if_isempty!(owners :: PathDocOwners, step :: Step)
        set_owners_line = get(owners, step)

        if set_owners_line != nothing
            if isempty(set_owners_line)
                Base.push!(owners.empty_steps, step)
                owners.valid = false
            end
        end
    end

    function to_string(owners :: PathDocOwners) :: String
        owners_text = "## Owners ## \n"
        println(owners.max_step)
        #! [for] $ O(S) $
        for step in 0:owners.max_step
            owners_text *= "$step => "
            if haskey(owners.table, step)
                set_owners_line_a = get(owners, step)
                #! [for] $ O(7) $
                for node_id in set_owners_line_a
                    key_node = Alias.as_key(node_id)
                    owners_text *= "$key_node,"
                end
            end
            owners_text *= "\n"
        end
        return owners_text
    end

    #=
    function to_string(owners :: PathDocOwners) :: String
        owners_text = "<div class=owners>"
        println(owners.max_step)
        for step in 0:owners.max_step
            owners_text *= "<div class=owners-step><div> $step </div>"
            if haskey(owners.table, step)
                set_owners_line_a = get(owners, step)
                owners_text *= "<div class=owners-list>"
                for node_id in set_owners_line_a
                    key_node = Alias.as_key(node_id)
                    owners_text *= "$key_node,"
                end
                owners_text *= "</div>"
            end

            owners_text *= "</div>"
        end
        owners_text *= "</div>"
        return owners_text
    end

    =#

end  # module
