module MapCollectionVars
    using Main.AbsSat.Alias: Step

    mutable struct MapColVars
        table :: Dict{String, Step}
    end

    function new()
        table = Dict{String, Step}()
        MapColVars(table)
    end

    function register_var!(col_vars :: MapColVars, title :: String, step :: Step)
        title = clean_title(title)
        col_vars.table[title] = step
    end

    function clean_title(title :: String)
        title = replace(title, "-"=>"")
        title = replace(title, "!"=>"")
        return title
    end

    function is_neg(title) :: Bool
        contains(title,"-") || contains(title,"!")
    end

    function get_step_var(col_vars :: MapColVars, title :: String) :: Union{Step, Nothing}
        have_neg = is_neg(title)
        title = clean_title(title)

        if haskey(col_vars.table, title)
            step = col_vars.table[title]
            if have_neg
                return step+1
            else
                return step
            end
        else
            return nothing
        end
    end

    function get_step_neg_var(col_vars :: MapColVars, title :: String) :: Union{Step, Nothing}
        if is_neg(title)
            title = clean_title(title)
        else
            title = "-$(title)"
        end

        return get_step_var(col_vars, title)
    end

end
