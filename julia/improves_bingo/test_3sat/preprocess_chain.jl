# Preproceso de renumeración de cadenas (4-oct-2026, rama reader-stuck; Lean `ForbidOnChainPre.lean`).
#
#   julia test_3sat/preprocess_chain.jl entrada.cnf salida.cnf
#
# Si la fórmula es una cadena de cláusulas (cada variable compartida, un «separador», está en dos cláusulas vecinas, y
# las cláusulas forman un camino), la reescribe en la clase Lean `ChainOrdN`:
#   * las cláusulas en el orden de la cadena;
#   * las variables numeradas en ese orden: las de dentro del primer bloque, s1, la de dentro del bloque 1, s2, …;
#   * en cada cláusula de en medio, (separador izquierdo, la de dentro, separador derecho), con los signos de entrada.
# Las soluciones se corresponden por el renombrado (Lean `Renaming`, `satisfiable_iff_of_renaming`). En el fichero de
# salida, una línea `c map old new` por variable.

function read_cnf(path)
    cls = Vector{Vector{Int}}(); nv = 0
    for ln in eachline(path)
        s = strip(ln)
        (isempty(s) || s[1] in ('c', '%')) && continue
        if s[1] == 'p'
            nv = parse(Int, split(s)[3]); continue
        end
        lits = filter(!=(0), parse.(Int, split(s)))
        isempty(lits) || push!(cls, lits)
    end
    return nv, cls
end

"""La cadena de `cls`: (orden de las cláusulas, separadores entre ellas), o `nothing` si no es una cadena."""
function chain_of(cls)
    occ = Dict{Int, Vector{Int}}()
    for (j, c) in enumerate(cls), v in unique(abs.(c))
        push!(get!(() -> Int[], occ, v), j)
    end
    any(length(js) > 2 for js in values(occ)) && return nothing
    seps = Set(v for (v, js) in occ if length(js) == 2)
    nseps(j) = count(v -> v in seps, unique(abs.(cls[j])))
    any(j -> nseps(j) > 2, eachindex(cls)) && return nothing
    start = findfirst(j -> nseps(j) <= 1, eachindex(cls))
    start === nothing && return nothing
    order = [start]; used = Set([start]); sepseq = Int[]
    while length(order) < length(cls)
        nxt = nothing
        for v in unique(abs.(cls[order[end]]))
            v in seps || continue
            for j in occ[v]
                j in used || (nxt = (j, v))
            end
        end
        nxt === nothing && return nothing
        push!(order, nxt[1]); push!(used, nxt[1]); push!(sepseq, nxt[2])
    end
    return order, sepseq
end

function preprocess(cls)
    ch = chain_of(cls)
    ch === nothing && return nothing
    order, sepseq = ch
    nb = length(order)
    newid = Dict{Int, Int}(); next = Ref(0)
    num(v) = haskey(newid, v) || (newid[v] = (next[] += 1))
    inner(j) = [v for v in unique(abs.(cls[order[j]])) if !(v in sepseq)]
    for j in 1:nb
        foreach(num, inner(j))
        j < nb && num(sepseq[j])
    end
    out = Vector{Vector{Int}}()
    for j in 1:nb
        c = cls[order[j]]
        lit(v) = (l = c[findfirst(x -> abs(x) == v, c)]; sign(l) * newid[v])
        if 1 < j < nb && length(inner(j)) == 1 && length(c) == 3
            push!(out, [lit(sepseq[j - 1]), lit(inner(j)[1]), lit(sepseq[j])])
        else
            push!(out, [sign(l) * newid[abs(l)] for l in c])
        end
    end
    return out, newid
end

function main(inp, outp)
    nv, cls = read_cnf(inp)
    r = preprocess(cls)
    if r === nothing
        println(basename(inp), "\tno es una cadena"); return
    end
    out, newid = r
    open(outp, "w") do io
        println(io, "c ", basename(inp), " renumerada en el orden de la cadena (test_3sat/preprocess_chain.jl)")
        for v in sort(collect(keys(newid)))
            println(io, "c map ", v, " ", newid[v])
        end
        println(io, "p cnf ", nv, " ", length(out))
        for c in out
            println(io, join(c, " "), " 0")
        end
    end
    println(basename(inp), "\t→ ", basename(outp), "\tbloques=", length(out))
end

main(ARGS[1], ARGS[2])
