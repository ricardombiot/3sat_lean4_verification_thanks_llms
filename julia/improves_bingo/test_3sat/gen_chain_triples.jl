# Cadenas de tríos consecutivos (4-oct-2026, rama reader-stuck): la cláusula j es (x_j, x_j+1, x_j+2), signos al azar,
# con x_0 = 0 y saltos x_{j+1} - x_j ∈ {1, 2}. Un salto de 2: corte de una variable; de 1: corte de dos.
#
#   julia test_3sat/gen_chain_triples.jl <saltos, p. ej. 2,1,2,2,1> <semilla> salida.cnf
using Random
function main(args)
    jumps = parse.(Int, split(args[1], ",")); rng = MersenneTwister(parse(Int, args[2])); out = args[3]
    xs = cumsum([0; jumps]); nv = xs[end] + 3
    open(out, "w") do io
        println(io, "c ", basename(out), ": tríos consecutivos, saltos ", args[1], ", semilla ", args[2])
        println(io, "p cnf ", nv, " ", length(xs))
        for x in xs
            println(io, join([rand(rng, Bool) ? y : -y for y in (x + 1):(x + 3)], " "), " 0")
        end
    end
    println(basename(out), "\tvariables=", nv, "\tcláusulas=", length(xs))
end
main(ARGS)
