include("./gen_3sat_cnf.jl")
using Dates
# Example:
# julia generator.jl n=10 l=7 c=27
function main(args)
    #println(args)
    params = Dict{String, Int64}()
    for argument in args
        parts = split(argument,"=")
        key = "$(parts[1])"
        value = parse(Int64,"$(parts[2])",base=10)
        params[key] = value
    end

    #println(params)
    n = params["n"]
    n_literals = params["l"]
    n_clauses = params["c"]
    today = Dates.today()
    base_set_name = replace("set$(n)$(n_literals)$(n_clauses)_$(today)","-" => "")
    #println(base_set_name)
    generator(base_set_name, n, n_literals, n_clauses)
end

function generator(base_set_name, n, n_literals, n_clauses)
    for i in 1:n
        name_file = "$(base_set_name)_i$(i)_v$(n_literals)_c$n_clauses.cnf"
        println("Generating... $name_file")
        instance = generate_3sat_cnf(n_literals, n_clauses)
        println("Writing... $name_file")
        write_file!(name_file, instance)
    end
end

function write_file!(name_file, content)
    open("./../output/instances/$name_file", "w") do io
           write(io, content)
    end;
end

main(ARGS)
