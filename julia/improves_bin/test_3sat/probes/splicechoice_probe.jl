# Elección de certificados empalmables (docs/context/escalera_reader.md §4.2μ, lema Splice.splice). Tríos Q = q1 < q2 < q3 con
# testigos en un estado (muestreo NQ por estado). Se muestrean hasta K certificados por {q1, q2} (σ) y por {q2, q3} (τ).
# Compatibles: los requisitos de los nodos de τ tras q2 que miran pasos ≤ paso(q2) los cumple σ.
#   BASE: fracción de pares (σ, τ) compatibles.  ∀τ∃σ / ∀σ∃τ: toda τ (σ) tiene alguna pareja compatible.
#   julia --project=../.. splicechoice_probe.jl f1.cnf ...
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
                σs = unique([c for c in (randchain(U, B, Dict(q1.id.step => [q1], s => [q2]), top) for _ in 1:K) if c !== nothing])
                τs = unique([c for c in (randchain(U, B, Dict(s => [q2], q3.id.step => [q3]), top) for _ in 1:K) if c !== nothing])
                (isempty(σs) || isempty(τs)) && (bump("sin certificados por pareja"); continue)
                compat(σ, τ) = all(j -> all(r -> r.step > s || r.step < 0 || σ[r.step+1].id == r, req(τ[j+1].id)), s+1:top)
                M = [compat(σ, τ) for σ in σs, τ in τs]
                bump("BASE pares", length(M)); bump("BASE compatibles", count(M))
                bump(all(j -> any(M[:, j]), 1:length(τs)) ? "∀τ∃σ ok" : "∀τ∃σ FALLA")
                bump(all(i -> any(M[i, :]), 1:length(σs)) ? "∀σ∃τ ok" : "∀σ∃τ FALLA")
                bump(any(M) ? "∃ par compatible ok" : "∃ par compatible FALLA (en la muestra)")
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
