# Volcado de un fallo de KeyTri (keytri_probe.jl): tablas por paso de x, y, w, y si el enlace y–w es x-compatible.
#   julia --project=../.. keytri_dump.jl f.cnf
include("./keytri_common.jl")
include_string(Main, split(read("./keytri_probe.jl", String), "function probe")[1] |> s -> replace(s, "include(\"./keytri_common.jl\")" => ""))
ix(a) = a === nothing ? "-" : string(a.index)
fmt(p) = "$(p.id.step):$(p.id.index)/$(ix(p.parent_id))/$(ix(p.gparent_id))"
done_ = Ref(0)
for_each_join(ARGS[1]) do J, top
    done_[] >= 2 && return
    for R in sampleR(J)
        done_[] >= 2 && return
        G = pinned(J, R); G.is_valid || continue
        U = tables(G)
        for k in unique([p.id for p in keys(U) if p.id.step == top - 1])
            xs = [x for x in keys(U) if x.id == k]
            for x in xs
                ok, y, w, l = tripin(U, x, top)
                ok && continue
                done_[] += 1
                println("== cima $top R=$R x=$(fmt(x)) y=$(fmt(y)) w=$(fmt(w)) l=$l  (#x con id k: $(length(xs)))")
                cxyw = all(l2 -> any(r -> r.id.step == l2 && r in U[w] && r in U[x], U[y]), 0:top)
                println("Cx(y,w) = $cxyw")
                for s in 0:top
                    f(T) = join(sort([fmt(p) for p in T if p.id.step == s]), " ")
                    println("  paso $s | x: $(f(U[x])) | y: $(f(U[y])) | w: $(f(U[w]))")
                end
                break
            end
            done_[] >= 2 && return
        end
    end
end
