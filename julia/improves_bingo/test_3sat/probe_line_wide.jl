# Las líneas de un camino de unidades, de un solo lado (4-oct-2026, rama reader-stuck; tras `probe_split_wide.jl`).
#
#   julia test_3sat/probe_line_wide.jl a.cnf b.cnf …
#
# La línea de la cláusula k ve el prefijo de k+1 cláusulas; `v` es una variable de la cláusula k, que es la última
# unidad, así que el lado de `v` es uno solo: hacia la izquierda. Unidades = cláusulas en el orden del fichero; z vive
# en lo(z) … hi(z) (cortado en k); el corte j (entre j y j+1) es S_j = {z : lo z ≤ j < hi z}. Mapa binario de Lean del
# prefijo: variable z en 2z+1, 2z+2; cláusula j, literal p, en 2n+2+3j+p; la ventana de s lee s, s-1, s-2.
#
# Se busca UNA ventana testigo λ para toda la línea, con X = lo que lee λ salvo v. Los cortes de pegado son los S_j con
# S_j \ {v} ⊆ X: en ellos coinciden las caras (de `capFull` con λ si el trío no lee todo X; si lo lee, las de
# `faces_sigma`, que coinciden con a0 en lo leído; en v coinciden todas las de P). Para cada trío ordenado (i, j, l):
# e = el primer corte, de v hacia la izquierda, que el trío lee entero (la cola; 0 si ninguno); las piezas de las
# unidades e+1 … k, partidas en los cortes de pegado, sin `Bad3` (sin contar v). Los subtriángulos de λ leen todo X:
# un solo nivel de descenso.
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

const WIT = Ref(-1)
const ALLW = Int[]

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
    # un testigo λ para toda la línea: X = lo que lee λ salvo v; se pega en los cortes con S_j \ {v} ⊆ X
    C = 2nv + 2
    named = Dict("cl_prev2" => C + 3(k - 2) + 2, "cl_prev1" => C + 3(k - 2) + 1, "cl_prev0" => C + 3(k - 2),
        "cl_cur2" => C + 3(k - 1) + 2, "cl_cur1" => C + 3(k - 1) + 1, "cl_cur0" => C + 3(k - 1),
        "var_vm1_pos" => 2(v - 1) + 1, "var_vm1_neg" => 2(v - 1) + 2, "var_v_pos" => 2v + 1, "var_v_neg" => 2v + 2)
    # la regla: el último literal de la cláusula anterior; si el corte k-1 es solo {v}, el de dos atrás
    single = k >= 2 && Set(S(k - 1)) == Set([v])
    named["rule"] = single && k >= 3 ? C + 3(k - 3) + 2 : C + 3(k - 2) + 2
    named["rule_s"] = single ? C + 3(k - 3) + 2 : C + 3(k - 2) + 2
    fixed = get(ENV, "FIXED_LAM", "")
    lams = isempty(fixed) ? collect(0:(N - 1)) : [named[fixed]]
    for lam in lams
        (0 <= lam < N) || continue
        X = setdiff(R[lam + 1], Set([v]))
        isempty(X) && continue
        G = [j for j in 1:(k - 1) if issubset(setdiff(Set(S(j)), Set([v])), X)]
        ok = true
        for i in 0:(N - 1), jj in 0:(N - 1), l in 0:(N - 1)
            W = union(R[i + 1], R[jj + 1], R[l + 1])
            bad3(M) = any(z1 in R[l + 1] && z2 in R[jj + 1] && z3 in R[i + 1] && z1 != z2 && z1 != z3 && z2 != z3
                for z1 in M, z2 in M, z3 in M)
            reg(a, b) = setdiff(intersect(unitvars(a, b), W), Set([v]))
            e = something(findfirst(j -> issubset(S(j), W), cuts), 0)
            e = e == 0 ? 0 : cuts[e]
            bs = [e; [j for j in G if j > e]; k]
            if any(bad3(reg(bs[t] + 1, bs[t + 1])) for t in 1:(length(bs) - 1))
                ok = false; break
            end
        end
        if ok
            WIT[] = lam
            get(ENV, "ALL_LAMS", "0") == "1" || return true
            push!(ALLW, lam)
        end
    end
    return !isempty(ALLW)
end

function main(path)
    nv, cls = read_cnf(path)
    lines = 0; good = 0; bad = Tuple[]; wits = Tuple[]
    for k in eachindex(cls), v in unique(abs.(cls[k]) .- 1)
        lines += 1
        if line_ok(nv, cls, k, v)
            good += 1; push!(wits, (k, v, WIT[]))
        else
            length(bad) < 6 && push!(bad, (k, v))
        end
    end
    println(basename(path), "\tlíneas=", lines, "\tcon base=", good, "\tsin base (k, v)=", bad)
    get(ENV, "SHOW_WIT", "0") == "1" && println("  testigos (k, v, λ): ", wits)
end

for p in ARGS
    main(p)
end
