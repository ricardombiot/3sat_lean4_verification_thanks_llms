#=
    Importador DIMACS para el mapa bin. Espejo de graph_map_import_cnf.jl, pero llamando a
    add_gate_bin! y sin el fusión raíz (new() ya lo crea).

    c  simple_v3_c2.cnf
        c
        p cnf 3 2
        1 -3 0
        2 3 -1 0
=#

function load_import_bin!(path_file :: String) :: GMapBin
    gmap = new()
    import_bin!(gmap, path_file)
    close_gates!(gmap)
    return gmap
end

function import_bin!(gmap :: GMapBin, path_file :: String)
    stage = "waiting_conf"
    for line in eachline(path_file)
        first_char = line[1]

        if first_char != 'c'
            if stage == "waiting_conf" && first_char == 'p'
                cnf_p!(gmap, line)
                stage = "reading_ors"
            elseif stage == "reading_ors"
                cnf_or!(gmap, line)
            end
        end
    end
end

function cnf_p!(gmap :: GMapBin, line :: String)
    is_valid_format = contains(line, "cnf")

    if is_valid_format
        configurations = split(line, " ")
        n_vars = parse(Int64, configurations[3], base=10)
        for var_name in 1:n_vars
            add_var!(gmap, "$var_name")
        end
    else
        throw("The format of file is not valid. We only support 3SAT .cnf")
    end
end

function cnf_or!(gmap :: GMapBin, line :: String)
    line = replace(line, "-" => "!")
    literals = split(line, " ")

    if length(literals) != 4
        throw("We only supports 3SAT...then: $line is invalid.")
    end

    literal1 = "$(literals[1])"
    literal2 = "$(literals[2])"
    literal3 = "$(literals[3])"

    add_gate_bin!(gmap, literal1, literal2, literal3)
end
