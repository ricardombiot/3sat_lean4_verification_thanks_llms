# PairExact en estados unidos fijados (BranchFull.PairExact con pins): todo enlace y–w de J|R (w ∈ T(y)) está en una
# cadena de J|R (un nodo por paso, poseídos dos a dos) que pasa por y y w.
#   julia --project=../.. pairexact_probe.jl f1.cnf ...
include("./keytri_common.jl")
include_string(Main, split(read("./keyexact_probe.jl", String), "const DEPTH")[1] |> s -> replace(s, "include(\"./keytri_common.jl\")" => ""))
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        for R in sampleR(J)
            G = pinned(J, R); G.is_valid || continue
            U = tables(G)
            for (y, Ty) in U, w in Ty
                (haskey(U, w) && w != y && y.id.step < w.id.step) || continue
                ok = chain_through(U, top, Dict(y.id.step => y, w.id.step => w))
                bump("PairExact $(ok ? "ok" : "FALLA")")
                ok || ex("PairExact FALLA $(basename(path)) cima $top R=$R y=$y w=$w")
            end
        end
    end
end
run_all(probe)
