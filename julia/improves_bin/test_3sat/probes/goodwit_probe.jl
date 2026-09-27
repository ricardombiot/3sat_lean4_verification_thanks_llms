# Elección de certificados empalmables (docs/context/ambfar.md §4.2μ, lema Splice.splice). Tríos Q = q1 < q2 < q3 con
# testigos en un estado (muestreo NQ por estado). Se muestrean hasta K certificados por {q1, q2} (σ) y por {q2, q3} (τ).
# Compatibles: los requisitos de los nodos de τ tras q2 que miran pasos ≤ paso(q2) los cumple σ.
# ¿Qué sufijos τ (por q2, q3) tienen prefijo compatible? BUENO (exacto, por búsqueda): hay una cadena por q1, q2 que en
# cada paso t de un requisito r que cruza (de un nodo de τ tras q2) pasa por un nodo de id r.
#   V1: para cada requisito r que cruza, algún testigo de Q en el paso de r tiene id r.
# Regla R_gw: τ por q2, q3 cuyos nodos por encima de paso(q2) poseen todo Q (R_todos) y cuyos requisitos que cruzan
# nombran, cada uno, un testigo BUENO de Q: w posee Q y {q1, q2, w} es clique con testigos. (Requisito a requisito.)
# ¿Existe tal τ? ¿Es BUENO (tiene prefijo compatible)? Muestreo de hasta K·4 τ de R_todos, filtrados por R_gw.
#   julia --project=../.. goodwit_probe.jl f1.cnf ...
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
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    isclause(l) = l >= 2nv + 2
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
                function isgood(τ)
                    cross = [(τ[j+1], r) for j in s+1:top for r in req(τ[j+1].id) if 0 <= r.step <= s]
                    fixed = Dict{Int, Vector{PathNodeId}}(q1.id.step => [q1], s => [q2])
                    for (_, r) in cross
                        cand = [x for x in get(fixed, r.step, get(B, r.step, PathNodeId[])) if x.id == r]
                        isempty(cand) && return false
                        fixed[r.step] = cand
                    end
                    randchain(U, B, fixed, top) !== nothing
                end
                wits(t) = [w for w in get(B, t, PathNodeId[]) if all(q -> owns(U, w, q), Q)]
                gwcache = Dict{Int, Vector{PathNodeId}}()
                goodwits(t) = get!(gwcache, t) do
                    [w for w in wits(t) if (P = unique([q1, q2, w]); isclique(U, P) && all(l -> wit(U, B, P, l), 0:top))]
                end
                fx = Dict{Int, Vector{PathNodeId}}(s => [q2], q3.id.step => [q3])
                for l in s+1:top
                    l == q3.id.step && continue
                    fx[l] = wits(l)
                end
                τs = unique([c for c in (randchain(U, B, fx, top) for _ in 1:(4K)) if c !== nothing])
                isempty(τs) && (bump("R_todos no existe τ"); continue)
                crossok(τ) = all(r -> any(w -> w.id == r, goodwits(r.step)),
                                 [r for j in s+1:top for r in req(τ[j+1].id) if 0 <= r.step <= s])
                sel = [τ for τ in τs if crossok(τ)]
                if isempty(sel)
                    bump("R_gw no existe τ (en la muestra)"); continue
                end
                g = [isgood(τ) for τ in sel]
                bump(all(g) ? "R_gw todo τ BUENO" : (any(g) ? "R_gw algún τ BUENO" : "R_gw ningún τ BUENO"))
                bump(all(g) ? "R_gw τ BUENOS" : "R_gw τ BUENOS", count(g)); bump("R_gw τ", length(g))
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
