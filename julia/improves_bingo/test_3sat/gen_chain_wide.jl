# Cadenas con bloques anchos (4-oct-2026, rama reader-stuck): varias variables de dentro por bloque.
#
#   julia test_3sat/gen_chain_wide.jl <n bloques> <w de dentro por bloque> <extra por bloque> <semilla> <cruzada 0|1> salida.cnf
#
# Bloque 0: a, b, s1. Bloque de en medio p: s_p, z_1 … z_w, s_{p+1}. Último: s_{n-1}, c, d. En cada bloque de en medio,
# las cláusulas del camino (s_p, z_1, z_2), (z_1, z_2, z_3), …, (z_{w-1}, z_w, s_{p+1}) (con w = 1: (s_p, z_1, s_{p+1}))
# y `extra` cláusulas más sobre tres variables del bloque al azar. Signos al azar. Con `cruzada = 1` la numeración se
# baraja (y las cláusulas también); con 0, en el orden de la cadena.

using Random

function gen(n, w, extra, seed, cross)
    rng = MersenneTwister(seed)
    nxt = Ref(0); new() = (nxt[] += 1)
    blocks = Vector{Vector{Int}}()
    a, b = new(), new(); s = new()
    push!(blocks, [a, b, s])
    for p in 1:(n - 2)
        zs = [new() for _ in 1:w]
        s2 = new()
        push!(blocks, [s; zs; s2]); s = s2
    end
    c, d = new(), new()
    push!(blocks, [s, c, d])
    nv = nxt[]
    sg(v) = rand(rng, Bool) ? v : -v
    cls = Vector{Vector{Int}}()
    for (k, B) in enumerate(blocks)
        if k == 1 || k == n
            push!(cls, sg.(B))
        else
            if length(B) == 3
                push!(cls, sg.(B))
            else
                for i in 1:(length(B) - 2)
                    push!(cls, sg.(B[i:i + 2]))
                end
            end
        end
        for _ in 1:extra
            push!(cls, sg.(shuffle(rng, B)[1:3]))
        end
    end
    if cross
        perm = randperm(rng, nv)
        cls = [[sign(l) * perm[abs(l)] for l in c] for c in shuffle(rng, cls)]
    end
    return nv, cls
end

function main(args)
    n, w, extra, seed = parse.(Int, args[1:4]); cross = args[5] == "1"; out = args[6]
    nv, cls = gen(n, w, extra, seed, cross)
    open(out, "w") do io
        println(io, "c ", basename(out), ": cadena de ", n, " bloques, ", w, " de dentro por bloque, ", extra,
            " extra, semilla ", seed, cross ? ", numeración cruzada" : ", en orden")
        println(io, "p cnf ", nv, " ", length(cls))
        for c in cls
            println(io, join(c, " "), " 0")
        end
    end
    println(basename(out), "\tvariables=", nv, "\tcláusulas=", length(cls))
end

main(ARGS)
