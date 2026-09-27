module CheckerCnf

  function test_all(list_solutions :: Array{BitArray{1},1}, path_file :: String) :: Bool
    for solution in list_solutions
        if !test(solution, path_file)
          return false
        end
    end

    return true
  end

  function test(solution :: BitArray{1}, path_file :: String) :: Bool
      is_sat = true

      stage = "waiting_conf"
      for line in eachline(path_file)
         first_char = line[1]

         if first_char != 'c'
           if stage == "waiting_conf" && first_char == 'p'
             stage = "reading_ors"
           elseif stage == "reading_ors"
             if !check_or!(solution, line)
               return false
             end
           end
         end
      end

      return is_sat
  end

  function check_or!(solution :: BitArray{1}, line :: String)
    literals = split(line, " ")

    if length(literals) != 4
      throw("We only supports 3SAT...then: $line is invalid.")
    end

    literal1 = parse(Int64, "$(literals[1])", base=10)
    literal2 = parse(Int64, "$(literals[2])", base=10)
    literal3 = parse(Int64, "$(literals[3])", base=10)

    literal1_value = get_value(solution, literal1)
    literal2_value = get_value(solution, literal2)
    literal3_value = get_value(solution, literal3)

    return literal1_value || literal2_value || literal3_value
  end


  function get_value(solution :: BitArray{1}, index_literal :: Int64) :: Bool
    is_literal_negative = index_literal < 0
    literal_value = solution[abs(index_literal)]
    if is_literal_negative
      return !literal_value
    else
      return literal_value
    end
  end


end
