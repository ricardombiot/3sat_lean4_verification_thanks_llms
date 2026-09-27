# KeyTri (M1Parts.lean): en J|R válido, toda clave k viva del paso top-1 tiene un nodo x (x.id = k) con TriPin:
#   y, w poseen x, w ∈ T(y) ⇒ en cada paso l ∃ r ∈ T(y) ∩ T(w) ∩ T(x) con r.step = l.
# KeyTri₁ (TriPinCut.TriPin₁): lo mismo tras una ronda de cortes: y, w poseen x con enlace Cx(y, w) ⇒ en cada paso l
#   ∃ r ∈ T(y) ∩ T(w) ∩ T(x), r.step = l, con Cx(y, r) y Cx(w, r). Cx(y, w): w ∈ T(y) y en cada paso un testigo que x posee.
# Se anota también si M1a-todas vale para esa clave (J|(R+k) válido), para separar los fallos.
#   julia --project=../.. keytri_probe.jl f1.cnf ...
include("./keytri_common.jl")
function tripin(U, x, top)
    Tx = U[x]
    for (y, Ty) in U
        x in Ty || continue
        for w in Ty
            (haskey(U, w) && x in U[w]) || continue
            Tw = U[w]
            for l in 0:top
                any(r -> r.id.step == l && r in Tw && r in Tx, Ty) || return (false, y, w, l)
            end
        end
    end
    (true, nothing, nothing, nothing)
end
function tripin1(U, x, top)
    Tx = U[x]
    memo = Dict{Tuple{PathNodeId, PathNodeId}, Bool}()
    cx(y, w) = get!(memo, (y, w)) do
        haskey(U, w) && w in U[y] &&
            all(l -> any(r -> r.id.step == l && r in U[w] && r in Tx, U[y]), 0:top)
    end
    for (y, Ty) in U
        x in Ty || continue
        for w in Ty
            (haskey(U, w) && x in U[w] && cx(y, w)) || continue
            Tw = U[w]
            for l in 0:top
                any(r -> r.id.step == l && r in Tw && r in Tx && cx(y, r) && cx(w, r), Ty) || return false
            end
        end
    end
    true
end
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        for R in sampleR(J)
            G = pinned(J, R)
            G.is_valid || continue
            U = tables(G)
            for k in unique([p.id for p in keys(U) if p.id.step == top - 1])
                xs = [x for x in keys(U) if x.id == k]
                res = [tripin(U, x, top) for x in xs]
                ok = any(r -> r[1], res)
                bump("KeyTri $(ok ? "ok" : "FALLA")")
                all(r -> r[1], res) || bump("KeyTri algún x falla")
                ok1 = any(x -> tripin1(U, x, top), xs)
                bump("KeyTri₁ $(ok1 ? "ok" : "FALLA")")
                ok1 || ex("KeyTri₁ FALLA $(basename(path)) cima $top R=$R k=$k")
                if !ok
                    m1a = pinned(J, vcat(R, [k])).is_valid
                    bump("KeyTri FALLA con M1a-todas $(m1a ? "ok" : "FALLA")")
                    _, y, w, l = res[1]
                    ex("KeyTri FALLA $(basename(path)) cima $top R=$R k=$k y=$y w=$w l=$l")
                end
            end
        end
    end
end
run_all(probe)
