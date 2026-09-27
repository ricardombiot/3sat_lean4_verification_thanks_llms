# KeyExact (BranchRel.PairExactRel en la clave): en J|R válido, para x de la clave (paso top-1), todo enlace y–w
# x-compatible (Cx) está en una cadena con x: un nodo por paso, todos poseídos dos a dos, pasando por x, y, w.
# DEPTH=D (por defecto 1): x en el paso top-D (0 = cima, 1 = claves; -1 = todos los pasos).
# Si vale, KeyTri₁ sale de BranchRel.triPin₁_of_pairExactRel.
#   julia --project=../.. keyexact_probe.jl f1.cnf ...
include("./keytri_common.jl")
function chain_through(U, top, fixed::Dict{Int, PathNodeId})
    bystep = [PathNodeId[] for _ in 0:top]
    for p in keys(U); 0 <= p.id.step <= top && push!(bystep[p.id.step + 1], p); end
    F = collect(values(fixed))
    cand = [haskey(fixed, l) ? [fixed[l]] : [s for s in bystep[l + 1] if all(f -> f in U[s] && s in U[f], F)] for l in 0:top]
    sel = PathNodeId[]
    function dfs(l)
        l > top && return true
        for s in cand[l + 1]
            all(p -> p in U[s] && s in U[p], sel) || continue
            push!(sel, s); dfs(l + 1) && return true; pop!(sel)
        end
        false
    end
    dfs(0)
end
const DEPTH = parse(Int, get(ENV, "DEPTH", "1"))
function probe(path, st)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 10 && (bump("ej"); println(s))
    for_each_join(path) do J, top
        for R in sampleR(J)
            G = pinned(J, R); G.is_valid || continue
            U = tables(G)
            for x in [p for p in keys(U) if DEPTH < 0 || p.id.step == top - DEPTH]
                Tx = U[x]
                cx(y, w) = haskey(U, w) && w in U[y] && all(l -> any(r -> r.id.step == l && r in U[w] && r in Tx, U[y]), 0:top)
                for (y, Ty) in U
                    x in Ty || continue
                    for w in Ty
                        (haskey(U, w) && x in U[w] && cx(y, w)) || continue
                        fixed = Dict(x.id.step => x, y.id.step => y, w.id.step => w)
                        length(fixed) == length(unique([x, y, w])) || (bump("KeyExact paso repetido"); continue)
                        ok = chain_through(U, top, fixed)
                        bump("KeyExact $(ok ? "ok" : "FALLA")")
                        ok || ex("KeyExact FALLA $(basename(path)) cima $top R=$R x=$x y=$y w=$w")
                    end
                end
            end
        end
    end
end
run_all(probe)
