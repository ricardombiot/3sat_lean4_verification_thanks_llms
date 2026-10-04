# El corte de un lado con bloques anchos (4-oct-2026, rama reader-stuck; tras `probe_split.jl`).
#
#   julia test_3sat/probe_split_wide.jl a.cnf b.cnf …
#
# La fórmula como camino de unidades: las cláusulas en el orden del fichero (una cadena en orden), la variable z vive
# en las unidades lo(z) … hi(z), y el corte k (entre las unidades k y k+1) es S_k = {z : lo z ≤ k < hi z} (uno o dos
# variables en las cadenas anchas). `v` es un corte de una sola variable; su lado derecho son las unidades siguientes
# hasta el final o hasta otro corte de una variable (extremo fijo). Mapa binario de Lean: v en los pasos 2v+1, 2v+2; la
# cláusula j, literal p, en 2n+2+3j+p; la ventana de k lee k, k-1, k-2.
#
# Para cada trío ordenado de ventanas (i, j, l) se busca la salida de `side_two`/`side_three` con cortes de unidad:
#   * una cola: el primer corte e del lado con S_e leído entero por el trío (o el extremo); detrás, `a0`;
#   * cortes intermedios k1 < k2 (a lo sumo dos) entre v y e, todos leídos enteros por UNA ventana testigo lam
#     (las caras de un testigo coinciden en lo que lee lam, y así se pegan en S_k);
#   * las regiones (las variables de las unidades entre cortes, sin v) sin `Bad3`; la primera (la de v), con a lo sumo
#     una variable leída (`estricta`) o solo sin `Bad3` (`laxa`, si todas las caras son de P).
# Salida: lados, lados con salida en todo trío (estricta / laxa), laxa con un solo corte intermedio, y sin cortes
# intermedios (solo cola).

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
    U = length(cls)
    vars(c) = unique(abs.(c) .- 1)
    lo = fill(typemax(Int), nv); hi = fill(-1, nv)
    for (u, c) in enumerate(cls), z in vars(c)
        lo[z + 1] = min(lo[z + 1], u); hi[z + 1] = max(hi[z + 1], u)
    end
    S(k) = [z for z in 0:(nv - 1) if lo[z + 1] <= k < hi[z + 1]]          # corte entre las unidades k y k+1
    single = [k for k in 1:(U - 1) if length(S(k)) == 1]
    N = 2nv + 3U + 3
    stepvar = Dict{Int, Int}()
    for z in 0:(nv - 1)
        stepvar[2z + 1] = z; stepvar[2z + 2] = z
    end
    for (j, c) in enumerate(cls), (p, lit) in enumerate(c)
        stepvar[2nv + 2 + 3(j - 1) + (p - 1)] = abs(lit) - 1
    end
    R = [Set(stepvar[k2] for k2 in (k, k - 1, k - 2) if k2 >= 0 && haskey(stepvar, k2)) for k in 0:(N - 1)]
    unitvars(a, b) = Set(z for z in 0:(nv - 1) if lo[z + 1] <= b && hi[z + 1] >= a)   # unidades a … b
    sides = 0; ok_s = 0; ok_l = 0; ok_tail = 0; ok_1 = 0; ex = Tuple[]
    for kv in single
        v = S(kv)[1]
        ends = [[k for k in single if k > kv]; U]
        for kb in ends
            sides += 1
            good_s = true; good_l = true; good_t = true; good_1 = true
            cuts = [k for k in (kv + 1):(kb - 1)]
            for i in 0:(N - 1), jj in 0:(N - 1), l in 0:(N - 1)
                W = union(R[i + 1], R[jj + 1], R[l + 1])
                bad3(M) = any(z1 in R[l + 1] && z2 in R[jj + 1] && z3 in R[i + 1] && z1 != z2 && z1 != z3 && z2 != z3
                    for z1 in M, z2 in M, z3 in M)
                e = something(findfirst(k -> issubset(S(k), W), cuts), length(cuts) + 1)
                eu = e <= length(cuts) ? cuts[e] : kb                         # la cola empieza tras la unidad eu
                reg(a, b) = setdiff(intersect(unitvars(a, b), W), Set([v]))
                function fits(ks, strict)
                    bs = [kv; ks; eu]
                    for t in 1:(length(bs) - 1)
                        M = reg(bs[t] + 1, bs[t + 1])
                        if t == 1 && strict
                            length(M) <= 1 || return false
                        else
                            bad3(M) && return false
                        end
                    end
                    return true
                end
                inner = [k for k in cuts if k < eu]
                lams = 0:(N - 1)
                tries(strict, two) = fits(Int[], strict) || any(lams) do lam
                    rk = [k for k in inner if issubset(S(k), R[lam + 1])]
                    any(fits([k], strict) for k in rk) ||
                        (two && any(fits([k1, k2], strict) for k1 in rk, k2 in rk if k1 < k2))
                end
                ts = tries(true, true); tl = ts || tries(false, true)
                tries(false, false) || (good_1 = false)
                ts || (good_s = false)
                tl || (good_l = false; length(ex) < 4 && push!(ex, (v, kv, kb, i, jj, l)))
                fits(Int[], false) || (good_t = false)
            end
            ok_s += good_s; ok_l += good_l; ok_tail += good_t; ok_1 += good_1
        end
    end
    println(basename(path), "\tunidades=", U, "\tlados=", sides, "\testricta=", ok_s, "\tlaxa=", ok_l,
        "\tun corte=", ok_1, "\tsolo cola=", ok_tail, "\tejemplos sin salida (v, kv, kb, i, j, l)=", ex)
end

for p in ARGS
    main(p)
end
