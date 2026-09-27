# CoverRow (M1bChain.lean) en todas las filas: J estado unido de la línea n+1 (cima top = n+1), R pins al azar, m una fila
# 1 ≤ m ≤ n con clave viva k_m en J|R. K = J|(R + k_m) válido ⇒ toda entrada (p, v) de K con p bajo la fila m-1 y v bajo
# la fila m está en J|(R + k_m + x) válido para alguna clave viva x de la fila m-1 de K.
#   julia --project=../.. coverrow_probe.jl f1.cnf ...
include("./keytri_common.jl")
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        n = top - 1
        for R in sampleR(J)
            G = pinned(J, R); G.is_valid || continue
            UG = tables(G)
            for m in 2:n
                for km in unique(x.id for x in keys(UG) if x.id.step == m)
                    km in R && continue
                    L = vcat(R, [km])
                    K = pinned(J, L); K.is_valid || continue
                    U = tables(K)
                    parts = Dict{Any, Any}()
                    for x in unique(y.id for y in keys(U) if y.id.step == m - 1)
                        Kx = pinned(J, vcat(L, [x])); Kx.is_valid && (parts[x] = tables(Kx))
                    end
                    for (p, Tp) in U
                        p.id.step < m - 1 || continue
                        for v in Tp
                            v.id.step < m || continue
                            ok = any(((x, Ux),) -> haskey(Ux, p) && v in Ux[p], parts)
                            bump("CoverRow $(m == n ? "fila n" : "fila < n") $(ok ? "ok" : "FALLA")")
                            ok || ex("CoverRow FALLA $(basename(path)) cima $top m=$m R=$R km=$km p=$(p.id) v=$(v.id)")
                        end
                    end
                end
            end
        end
    end
end
run_all(probe)
