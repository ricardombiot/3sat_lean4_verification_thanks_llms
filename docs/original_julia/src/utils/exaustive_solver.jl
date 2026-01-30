module ExhaustiveSolver

    mutable struct ExSolver
        path_file :: String
        list_solutions :: Array{BitArray{1},1}
        gates_or :: Array{Array{Int64,1},1}

        n_literals :: Int64
        current_case :: Int64
        last_case :: Int64
    end

    function new(path_file :: String) :: ExSolver
        list_solutions = Array{BitArray{1},1}()
        gates_or = Array{Array{Int64,1},1}()
        n_literals = 0
        current_case = 0
        last_case = 0
        solver = ExSolver(path_file, list_solutions, gates_or, n_literals, current_case, last_case)
        init!(solver)
        return solver
    end

    function init!(solver :: ExSolver)
        read_cnf_file!(solver)
        solver.last_case = (2^solver.n_literals)-1
    end

    function read_cnf_file!(solver :: ExSolver)
        stage = "waiting_conf"
        for line in eachline(solver.path_file)
           first_char = line[1]

           if first_char != 'c'
             if stage == "waiting_conf" && first_char == 'p'
                 configurations = split(line, " ")
                 solver.n_literals = parse(Int64,configurations[3],base=10)

                 stage = "reading_ors"
             elseif stage == "reading_ors"
                 or_literals = read_or(line)
                 push!(solver.gates_or, or_literals)
             end
           end
        end
    end

    function read_or(line) :: Array{Int64,1}
        literals = split(line, " ")

        if length(literals) != 4
          throw("We only supports 3SAT...then: $line is invalid.")
        end

        literal1 = parse(Int64, "$(literals[1])", base=10)
        literal2 = parse(Int64, "$(literals[2])", base=10)
        literal3 = parse(Int64, "$(literals[3])", base=10)

        return [literal1,literal2,literal3]
    end


    function run!(solver :: ExSolver)
        while solver.current_case != solver.last_case+1
            if check_case!(solver)
                register_as_solution!(solver)
            end
            solver.current_case += 1
        end
    end

    function check_case!(solver :: ExSolver) :: Bool
        current_case_bits = case_to_bits(solver.current_case)

        for or_literals in solver.gates_or
            if !calc_or(current_case_bits, or_literals)
                return false
            end
        end

        return true
    end

    function register_as_solution!(solver :: ExSolver)
        case_chars_bits = reverse(bitstring(solver.current_case))
        txt_solution = case_chars_bits[1:solver.n_literals]

        solution = BitArray([])
        for ch in txt_solution
            if ch == '1'
                push!(solution, true)
            else
                push!(solution, false)
            end
        end

        push!(solver.list_solutions, solution)
    end

    function case_to_bits(current_case :: Int64) :: String
        case_chars_bits = reverse(bitstring(current_case))
        return case_chars_bits
    end

    function calc_or(current_case_bits :: String, or_literals :: Array{Int64,1}) :: Bool
        value1 = get_value(current_case_bits, or_literals[1])
        value2 = get_value(current_case_bits, or_literals[2])
        value3 = get_value(current_case_bits, or_literals[3])

        return value1 || value2 || value3
    end

    function get_value(current_case_bits :: String, index :: Int64) :: Bool
        is_neg = index < 0
        ch_bit_value = current_case_bits[abs(index)]

        if ch_bit_value == '1'
            bit = true
        else
            bit = false
        end

        if is_neg
            bit = !bit
        end

        return bit
    end


end
