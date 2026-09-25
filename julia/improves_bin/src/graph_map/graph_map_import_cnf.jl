#=
c  simple_v3_c2.cnf
    c
    p cnf 3 2
    1 -3 0
    2 3 -1 0
=#

function load_import!(path_file :: String) :: GMap
  gmap = new()
  import!(gmap, path_file)
  close_gates!(gmap)
  return gmap
end

function import!(gmap :: GMap, path_file :: String)
    stage = "waiting_conf"
    for line in eachline(path_file)
       #println(line)
       first_char = line[1]

       if first_char != 'c'
         #println(first_char)
         if stage == "waiting_conf" && first_char == 'p'
           #println("Call cnf_p")
           cnf_p!(gmap, line)
           stage = "reading_ors"
         elseif stage == "reading_ors"
           cnf_or!(gmap, line)
         end
       end
    end
end

function cnf_p!(gmap :: GMap, line :: String)
    is_valid_format = contains(line, "cnf")

    if is_valid_format
      #println("is valid format")
      configurations = split(line, " ")
      n_vars = parse(Int64,configurations[3],base=10)
      #println("NVARS: $n_vars")
      for var_name in 1:n_vars
        #println("create var... $var_name")
        add_var!(gmap, "$var_name")
      end
    else
      throw("The format of file is not valid. We only support 3SAT .cnf")
    end
end

function cnf_or!(gmap :: GMap, line :: String)
    line = replace(line, "-" => "!")
    literals = split(line, " ")

    if length(literals) != 4
      throw("We only supports 3SAT...then: $line is invalid.")
    end

    #println(literals)

    literal1 = "$(literals[1])"
    literal2 = "$(literals[2])"
    literal3 = "$(literals[3])"

    #println(" $literal1, $literal2, $literal3 ")
    add_gate!(gmap, literal1, literal2, literal3)
end
