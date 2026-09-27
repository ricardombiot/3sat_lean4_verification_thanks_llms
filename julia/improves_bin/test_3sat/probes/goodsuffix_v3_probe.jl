# Elección de certificados empalmables (docs/context/ambfar.md §4.2μ, lema Splice.splice). Tríos Q = q1 < q2 < q3 con
# testigos en un estado (muestreo NQ por estado). Se muestrean hasta K certificados por {q1, q2} (σ) y por {q2, q3} (τ).
# Compatibles: los requisitos de los nodos de τ tras q2 que miran pasos ≤ paso(q2) los cumple σ.
# ¿Qué sufijos τ (por q2, q3) tienen prefijo compatible? BUENO (exacto, por búsqueda): hay una cadena por q1, q2 que en
# cada paso t de un requisito r que cruza (de un nodo de τ tras q2) pasa por un nodo de id r.
#   V1: para cada requisito r que cruza, algún testigo de Q en el paso de r tiene id r.
#   V2: y ese testigo posee además el nodo de τ que exige r.
#   V3 (conjunta): hay una elección de un nodo de id r por cada requisito r que cruza tal que Q ∪ {esos nodos} es clique
#       con testigos (restringida a los pasos ≤ paso(q2): los de la parte del prefijo).
# Tabla BUENO × V2 y BUENO × V3.
#   julia --project=../.. goodsuffix_v3_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(67)
const NQ = parse(Int, get(ENV, "NQ", "30"))
const K = parse(Int, get(ENV, "K", "12"))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
function randchain(U, B, fixed, top)
    sel = Dict{Int, PathNodeId}()
    function go(l)
        l < 0 && return true
        for c in shuffle(haskey(fixed, l) ? fixed[l] : get(B, l, PathNodeId[]))
            all(p -> owns(U, c, p) && owns(U, p, c), values(sel)) || continue
            sel[l] = c
            go(l - 1) && return true
            delete!(sel, l)
        end
        false
    end
    go(top) ? [sel[l] for l in 0:top] : nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k, v = 1) = (st[k] = get(st, k, 0) + v)
    reqs = Dict{NodeId, Vector{NodeId}}()
    req(id) = get!(reqs, id) do; collect(SatMachine.map_get_node(gmap, id).requires); end
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            U = tables(g); B = bystep_of(U); ns = collect(keys(U))
            prs = [(a, b) for a in ns for b in ns if a.id.step < b.id.step && owns(U, a, b)]
            isempty(prs) && return
            cnt = 0
            for _ in 1:(30 * NQ)
                cnt >= NQ && break
                (a, b) = rand(prs)
                cs = [x for x in ns if x.id.step > b.id.step && owns(U, a, x) && owns(U, b, x)]
                isempty(cs) && continue
                Q = [a, b, rand(cs)]
                (isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)) || continue
                cnt += 1
                q1, q2, q3 = Q; s = q2.id.step
                τs = unique([c for c in (randchain(U, B, Dict(s => [q2], q3.id.step => [q3]), top) for _ in 1:K) if c !== nothing])
                for τ in τs
                    cross = [(τ[j+1], r) for j in s+1:top for r in req(τ[j+1].id) if 0 <= r.step <= s]
                    fixed = Dict{Int, Vector{PathNodeId}}(q1.id.step => [q1], s => [q2])
                    okfix = true
                    for (_, r) in cross
                        cand = [x for x in get(fixed, r.step, get(B, r.step, PathNodeId[])) if x.id == r]
                        isempty(cand) && (okfix = false)
                        fixed[r.step] = cand
                    end
                    good = okfix && randchain(U, B, fixed, top) !== nothing
                    wits(t) = [w for w in get(B, t, PathNodeId[]) if all(q -> owns(U, w, q), Q)]
                    v1 = all(p -> any(w -> w.id == p[2], wits(p[2].step)), cross)
                    v2 = all(p -> any(w -> w.id == p[2] && owns(U, w, p[1]), wits(p[2].step)), cross)
                    bump("BUENO=$good V2=$v2")
                    # V3: joint choice; Q restricted to the prefix members q1, q2
                    crs = unique([p[2] for p in cross])
                    opts = [[x for x in get(B, r.step, PathNodeId[]) if x.id == r] for r in crs]
                    function v3search(i, chosen)
                        if i > length(crs)
                            P = vcat([q1, q2], chosen)
                            return isclique(U, P) && all(l -> wit(U, B, P, l), 0:top)
                        end
                        for x in opts[i]
                            (x in chosen || x.id.step in (q1.id.step, s)) && (x in (q1, q2) || continue)
                            v3search(i + 1, vcat(chosen, x in (q1, q2) ? PathNodeId[] : [x])) && return true
                        end
                        false
                    end
                    v3 = all(!isempty, opts) && v3search(1, PathNodeId[])
                    bump("BUENO=$good V3=$v3")
                end
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
