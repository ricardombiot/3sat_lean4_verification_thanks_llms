# Comprobación estática de `SideSplit` (4-oct-2026, rama reader-stuck; Lean `ForbidOnChainAny.lean`).
# Los bloques son las cláusulas unidas por compartir dos variables o más: valen varias cláusulas y varias variables de
# dentro por bloque (`anchura`: el máximo de variables de dentro de un bloque de en medio).
#
#   julia test_3sat/probe_split.jl a.cnf b.cnf …
#
# No corre la máquina: lo que lee un triángulo depende solo de los pasos de sus nodos. Con el mapa binario de Lean
# (variable v desde 0 en los pasos 2v+1 y 2v+2; la cláusula j, literal p, en el paso 2n+2+3j+p; la ventana del paso k
# lee k, k-1, k-2), para cada lado (m, b) de la cadena (bloques m … b-1 a la derecha del separador m) y cada trío
# ordenado de pasos (i, j, l): el primer separador leído r; si r ≥ 2, ¿hay un corte 1 ≤ c < r con las dos regiones
# buenas? Una región es mala si tiene tres variables distintas leídas, una en la ventana l, otra en la j y otra en la i.
# Salida por instancia: lados, lados en los que siempre hay corte, y los tríos sin corte (los primeros).

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

function main(path)
    nv, cls = read_cnf(path)
    vars(c) = unique(abs.(c) .- 1)                      # desde 0
    # los bloques: las cláusulas unidas por compartir dos variables o más (varias cláusulas y anchura por bloque)
    par = collect(eachindex(cls))
    find(x) = par[x] == x ? x : (par[x] = find(par[x]))
    for j in eachindex(cls), j2 in (j + 1):length(cls)
        length(intersect(vars(cls[j]), vars(cls[j2]))) >= 2 && (par[find(j)] = find(j2))
    end
    roots = unique(find.(eachindex(cls)))
    bvars = [sort(unique(reduce(vcat, [vars(cls[j]) for j in eachindex(cls) if find(j) == r]))) for r in roots]
    occ = Dict{Int, Vector{Int}}()
    for (g, vs) in enumerate(bvars), v in vs
        push!(get!(() -> Int[], occ, v), g)
    end
    seps = Set(v for (v, gs) in occ if length(gs) >= 2)
    # el orden de la cadena: empezar por un bloque con un solo separador
    nseps(g) = count(v -> v in seps, bvars[g])
    start = findfirst(g -> nseps(g) == 1, eachindex(bvars))
    order = [start]; used = Set([start]); sepseq = Int[]
    while length(order) < length(bvars)
        cur = order[end]; nxt = nothing
        for v in bvars[cur]
            v in seps || continue
            for g in occ[v]
                g in used && continue
                nxt = (g, v)
            end
        end
        nxt === nothing && break
        push!(order, nxt[1]); push!(used, nxt[1]); push!(sepseq, nxt[2])
    end
    nb = length(order)
    zone = Dict{Int, Int}()                              # interior del bloque k: k; separador i: nb + i
    for (k, g) in enumerate(order), v in bvars[g]
        v in seps || (zone[v] = k - 1)
    end
    for (i, v) in enumerate(sepseq)
        zone[v] = nb + i
    end
    width = maximum(count(v -> get(zone, v, -1) == k, keys(zone)) for k in 1:(nb - 2); init = 0)
    sv = Dict(i => v for (i, v) in enumerate(sepseq))
    # el mapa: paso → variable
    N = 2nv + 3length(cls) + 3
    stepvar = Dict{Int, Int}()
    for v in 0:(nv - 1)
        stepvar[2v + 1] = v; stepvar[2v + 2] = v
    end
    for (j, c) in enumerate(cls), (p, lit) in enumerate(c)
        stepvar[2nv + 2 + 3(j - 1) + (p - 1)] = abs(lit) - 1
    end
    reads(k) = Set(stepvar[k2] for k2 in (k, k - 1, k - 2) if k2 >= 0 && haskey(stepvar, k2))
    R = [reads(k) for k in 0:(N - 1)]
    sides = 0; okside = 0; bad = Tuple[]
    for m in 1:(nb - 1), b in (m + 1):nb
        sides += 1; good = true
        for i in 0:(N - 1), jj in 0:(N - 1), l in 0:(N - 1)
            W = union(R[i + 1], R[jj + 1], R[l + 1])
            L = b - m
            r = something(findfirst(k -> sv[m + k] in W, 1:(L - 1)), L)
            r >= 2 || continue
            function bad3(M)
                zs = [z for z in W if M(z)]
                for z1 in zs, z2 in zs, z3 in zs
                    (z1 != z2 && z1 != z3 && z2 != z3) || continue
                    (z1 in R[l + 1] && z2 in R[jj + 1] && z3 in R[i + 1]) && return true
                end
                return false
            end
            zn(z) = get(zone, z, -1)
            ok = any(1:(r - 1)) do c
                A(z) = m <= zn(z) < m + c
                B(z) = (m + c <= zn(z) < m + r) || (m + r < b && zn(z) == nb + m + r)
                !bad3(A) && !bad3(B)
            end
            if !ok
                good = false
                length(bad) < 5 && push!(bad, (m, b, i, jj, l, r))
            end
        end
        okside += good
    end
    println(basename(path), "\tbloques=", nb, "\tanchura=", width, "\tlados=", sides, "\tcon corte=", okside, "\tejemplos sin corte=", bad)
end

for p in ARGS
    main(p)
end
