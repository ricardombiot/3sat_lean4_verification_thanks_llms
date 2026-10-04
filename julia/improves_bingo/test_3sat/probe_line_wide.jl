# Las líneas de un camino de unidades, de un solo lado (4-oct-2026, rama reader-stuck; tras `probe_split_wide.jl`).
#
#   julia test_3sat/probe_line_wide.jl a.cnf b.cnf …
#
# La línea de la cláusula k ve el prefijo de k+1 cláusulas; `v` es una variable de la cláusula k, que es la última
# unidad, así que el lado de `v` es uno solo: hacia la izquierda. Unidades = cláusulas en el orden del fichero; z vive
# en lo(z) … hi(z) (cortado en k); el corte j (entre j y j+1) es S_j = {z : lo z ≤ j < hi z}. Mapa binario de Lean del
# prefijo: variable z en 2z+1, 2z+2; cláusula j, literal p, en 2n+2+3j+p; la ventana de s lee s, s-1, s-2.
#
# Para cada trío ordenado (i, j, l): e = el primer corte, de v hacia la izquierda (j = lo v - 1, lo v - 2, …), que el
# trío lee entero (o -1: el principio). Se busca una base c0 (un corte j ≤ lo v - 1, la misma para todos los tríos de
# la línea) con:
#   * si e ≥ c0 (base): la región de v, las unidades e+1 … k, sin `Bad3` (caras de P: `faces_sigma`); la región de v
#     se parte gratis en los cortes que son solo {v} (todas las caras de P coinciden en v);
#   * si e < c0 (abierto): una ventana testigo que lee entero S_{c0} (sus subtriángulos lo leen y caen en la base), y
#     las regiones c0+1 … k (la de v) y e+1 … c0 sin `Bad3` (caras de `capFull`, todas de P).
# Salida por instancia: líneas, líneas con base, y las primeras sin base.

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

function line_ok(nv, cls, k, v)
    pre = cls[1:k]                                   # unidades 1 … k (la k es la de la línea)
    vars(c) = unique(abs.(c) .- 1)
    lo = fill(typemax(Int), nv); hi = fill(-1, nv)
    for (u, c) in enumerate(pre), z in vars(c)
        lo[z + 1] = min(lo[z + 1], u); hi[z + 1] = max(hi[z + 1], u)
    end
    S(j) = [z for z in 0:(nv - 1) if lo[z + 1] <= j < hi[z + 1]]
    unitvars(a, b) = Set(z for z in 0:(nv - 1) if lo[z + 1] <= b && hi[z + 1] >= a)
    N = 2nv + 3length(pre) + 3
    stepvar = Dict{Int, Int}()
    for z in 0:(nv - 1)
        stepvar[2z + 1] = z; stepvar[2z + 2] = z
    end
    for (j, c) in enumerate(pre), (p, lit) in enumerate(c)
        stepvar[2nv + 2 + 3(j - 1) + (p - 1)] = abs(lit) - 1
    end
    R = [Set(stepvar[s2] for s2 in (s, s - 1, s - 2) if s2 >= 0 && haskey(stepvar, s2)) for s in 0:(N - 1)]
    lv = lo[v + 1]
    vcuts = [j for j in lv:(k - 1) if S(j) == [v]]
    cuts = collect((lv - 1):-1:1)                     # de v hacia la izquierda
    wit(c0) = any(issubset(S(c0), R[s + 1]) for s in 0:(N - 1))
    cands = [c0 for c0 in [cuts; 0] if c0 == 0 || wit(c0)]
    for c0 in cands
        ok = true
        for i in 0:(N - 1), jj in 0:(N - 1), l in 0:(N - 1)
            W = union(R[i + 1], R[jj + 1], R[l + 1])
            bad3(M) = any(z1 in R[l + 1] && z2 in R[jj + 1] && z3 in R[i + 1] && z1 != z2 && z1 != z3 && z2 != z3
                for z1 in M, z2 in M, z3 in M)
            reg(a, b) = setdiff(intersect(unitvars(a, b), W), Set([v]))        # `v`, de P: aparte (`hpv`)
            # la región de v se parte en los cortes que son solo {v} (las caras de P coinciden en v)
            function vbad(a)
                bs = [a - 1; vcuts[vcuts .>= a]; k]
                any(bad3(reg(bs[t] + 1, bs[t + 1])) for t in 1:(length(bs) - 1))
            end
            e = something(findfirst(j -> issubset(S(j), W), cuts), 0)
            e = e == 0 ? 0 : cuts[e]
            if e >= c0
                vbad(e + 1) && (ok = false; break)
            else
                (vbad(c0 + 1) || bad3(reg(e + 1, c0))) && (ok = false; break)
            end
        end
        ok && return true
    end
    return false
end

function main(path)
    nv, cls = read_cnf(path)
    lines = 0; good = 0; bad = Tuple[]
    for k in eachindex(cls), v in unique(abs.(cls[k]) .- 1)
        lines += 1
        if line_ok(nv, cls, k, v)
            good += 1
        else
            length(bad) < 6 && push!(bad, (k, v))
        end
    end
    println(basename(path), "\tlíneas=", lines, "\tcon base=", good, "\tsin base (k, v)=", bad)
end

for p in ARGS
    main(p)
end
