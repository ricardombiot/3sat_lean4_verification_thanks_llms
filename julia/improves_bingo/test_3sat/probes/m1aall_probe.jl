# M1aAll (M1Parts.lean): en J|R válido, fijar la clave de cualquier nodo vivo del paso top-1 deja J válido.
# Sin piezas (más rápida que m1split_probe.jl), para cubrir más corpus.
#   julia --project=../.. m1aall_probe.jl f1.cnf ...
include("./keytri_common.jl")
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        for R in sampleR(J)
            G = pinned(J, R)
            G.is_valid || continue
            ks = unique([p.id for p in keys(tables(G)) if p.id.step == top - 1])
            tag = length(ks) >= 2 ? "≥2 claves" : "1 clave"
            for k in ks
                ok = pinned(J, vcat(R, [k])).is_valid
                bump("M1aAll ($tag) $(ok ? "ok" : "FALLA")")
                ok || ex("M1aAll FALLA $(basename(path)) cima $top R=$R k=$k")
            end
        end
    end
end
run_all(probe)
