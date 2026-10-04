# Forma truncada de M1bLowOwn (escalera_reader.md §4.2ο.2): el kernel K = J|(R+k) sin la cima, ¿se parte por las claves i
# de la fila n-1 = top-2? (paso Split de la reducción M1b(n) ⇐ M1b(n-1) + Split(n-1)).
#   LinkSplit: todo enlace (a, b) de K con a, b bajo la fila n-1 es x-compatible para algún nodo x de la fila n-1
#              (en cada paso l hay r ∈ T(a) ∩ T(b) ∩ T(x); x posee a y b).
#   PartValid: para cada clave i viva en la fila n-1 de K, J|(R+k+i) es válido (el trozo i no muere al fijarlo).
#   CoverSplit: todo enlace (a, b) de K con a bajo la fila n-1 es enlace de K_{k,i} = J|(R+k+i) para alguna clave i
#               (K es la unión de sus trozos por la fila n-1; con la igualdad W = K, es la forma cerrada de LinkSplit).
#   julia --project=../.. split_probe.jl f1.cnf ...
include("./keytri_common.jl")
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        top >= 3 || return
        n1 = top - 2                                     # fila n-1 (la de las claves de las fuentes)
        for R in sampleR(J)
            G = pinned(J, R); G.is_valid || continue
            for k in unique(x.id for x in keys(tables(G)) if x.id.step == top - 1)
                K = pinned(J, vcat(R, [k])); K.is_valid || continue
                U = tables(K)
                xs = [x for x in keys(U) if x.id.step == n1]
                cx(a, b, x) = x in U[a] && x in U[b] &&
                    all(l -> any(r -> r.id.step == l && r in U[b] && r in U[x], U[a]), 0:top)
                for (a, Ta) in U
                    a.id.step < n1 || continue
                    for b in Ta
                        (haskey(U, b) && b.id.step < n1) || continue
                        ok = any(x -> cx(a, b, x), xs)
                        bump("LinkSplit $(ok ? "ok" : "FALLA")")
                        ok || ex("LinkSplit FALLA $(basename(path)) cima $top R=$R k=$k a=$(a.id) b=$(b.id)")
                    end
                end
                parts = Dict{Any, Any}()
                for i in unique(x.id for x in xs)
                    Ki = pinned(J, vcat(R, [k, i]))
                    bump("PartValid $(Ki.is_valid ? "ok" : "FALLA")")
                    Ki.is_valid && (parts[i] = tables(Ki))
                end
                for (a, Ta) in U
                    a.id.step < n1 || continue
                    for b in Ta
                        haskey(U, b) || continue
                        ok = any(((i, Ui),) -> haskey(Ui, a) && b in Ui[a], parts)
                        bump("CoverSplit $(ok ? "ok" : "FALLA")")
                        ok || ex("CoverSplit FALLA $(basename(path)) cima $top R=$R k=$k a=$(a.id) b=$(b.id)")
                    end
                end
            end
        end
    end
end
run_all(probe)
