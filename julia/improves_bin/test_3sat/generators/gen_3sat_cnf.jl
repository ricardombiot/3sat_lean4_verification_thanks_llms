using Dates
using Random


function generate_3sat_cnf(n_literals, n_clauses) :: String
    today = Dates.today()
    result = "c 3SAT random generation...\n"
    result *= "c $today \n"
    result *= "p cnf $n_literals $n_clauses\n"

    list_literals = Vector(1:n_literals)
    for c in 1:n_clauses
        random_literals = shuffle(list_literals)

        for i in 1:3
            result *= add_literal(random_literals[i])
        end
        result *= "0\n"
    end

    return result
end

function add_literal(literal :: Int64) :: String
    result = ""
    is_negative = rand((0, 1)) == 0

    if is_negative
        result = "-"
    end
    result *= "$literal "
    return result
end
