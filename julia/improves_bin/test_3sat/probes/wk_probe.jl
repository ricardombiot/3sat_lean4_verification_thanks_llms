# ¿KFix = M1bLowOwn? (escalera_reader.md §4.2ο.2). En J|R válido y para cada clave viva k: el mayor conjunto de enlaces
# cerrado para k (W_k, por iteración) frente a los enlaces de K_k = J|(R+k) (el pin de la clave con su review).
# Deducido: W_k es simétrico, con lazos, y su testigo en el paso de al lado es padre/hijo ⇒ es un kernel por debajo de J
# que solo nombra k en la fila de claves ⇒ W_k ⊆ K_k; y K_k es cerrado para k ⇒ K_k ⊆ W_k. Si vale, W_k = K_k.
#   julia --project=../.. wk_probe.jl f1.cnf ...
include("./keytri_common.jl")
function gfp(U, kof, k, top)
    S = Set{Tuple{PathNodeId, PathNodeId}}()
    for (a, Ta) in U, b in Ta; haskey(U, b) && push!(S, (a, b)); end
    nb = Dict{PathNodeId, Set{PathNodeId}}()
    for (a, b) in S; push!(get!(nb, a, Set{PathNodeId}()), b); end
    changed = true
    while changed
        changed = false
        bad = [(a, b) for (a, b) in S if !all(l -> any(r -> r.id.step == l && r in get(nb, b, Set{PathNodeId}()) &&
                                                           k in kof[r], get(nb, a, Set{PathNodeId}())), 0:top)]
        for (a, b) in bad; delete!(S, (a, b)); delete!(nb[a], b); changed = true; end
    end
    S
end
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        for R in sampleR(J)
            G = pinned(J, R); G.is_valid || continue
            U = tables(G)
            kof = Dict(r => Set(x.id for x in T if x.id.step == top - 1) for (r, T) in U)
            for k in unique(x.id for x in keys(U) if x.id.step == top - 1)
                W = gfp(U, kof, k, top)
                K = pinned(J, vcat(R, [k]))
                KL = K.is_valid ? Set((a, b) for (a, T) in tables(K) for b in T) : Set{Tuple{PathNodeId, PathNodeId}}()
                eq = W == KL
                bump("W_k = K_k $(eq ? "ok" : "DISTINTOS")")
                eq || ex("DISTINTOS $(basename(path)) cima $top R=$R k=$k |W|=$(length(W)) |K|=$(length(KL)) W∖K=$(length(setdiff(W, KL))) K∖W=$(length(setdiff(KL, W)))")
            end
        end
    end
end
run_all(probe)
