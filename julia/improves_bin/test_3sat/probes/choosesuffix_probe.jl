# Elección de certificados empalmables (docs/context/escalera_reader.md §4.2μ, lema Splice.splice). Tríos Q = q1 < q2 < q3 con
# testigos en un estado (muestreo NQ por estado). Se muestrean hasta K certificados por {q1, q2} (σ) y por {q2, q3} (τ).
# Compatibles: los requisitos de los nodos de τ tras q2 que miran pasos ≤ paso(q2) los cumple σ.
# ¿Qué sufijos τ (por q2, q3) tienen prefijo compatible? BUENO (exacto, por búsqueda): hay una cadena por q1, q2 que en
# cada paso t de un requisito r que cruza (de un nodo de τ tras q2) pasa por un nodo de id r.
#   V1: para cada requisito r que cruza, algún testigo de Q en el paso de r tiene id r.
# Reglas para ELEGIR el sufijo desde los testigos de Q (sin conocer una cadena por Q):
#   R_cláusula: τ por q2, q3 que en cada paso de cláusula > paso(q2) pasa por un testigo de Q.
#   R_todos:    τ por q2, q3 cuyos nodos por encima de paso(q2) poseen todo Q.
# Para cada regla: ¿existe tal τ? ¿es BUENO (tiene prefijo compatible)?
#   julia --project=../.. choosesuffix_probe.jl f1.cnf ...
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
                for (rname, inR) in (("R_cláusula", l -> isclause(l)), ("R_todos", l -> true))
                    fx = Dict{Int, Vector{PathNodeId}}(s => [q2], q3.id.step => [q3])
                    for l in s+1:top
                        (l == q3.id.step || !inR(l)) && continue
                        fx[l] = wits(l)
                    end
                    τs = unique([c for c in (randchain(U, B, fx, top) for _ in 1:K) if c !== nothing])
                    if isempty(τs)
                        bump("$rname no existe τ"); continue
                    end
                    g = [isgood(τ) for τ in τs]
                    bump(all(g) ? "$rname todo τ BUENO" : (any(g) ? "$rname algún τ BUENO" : "$rname ningún τ BUENO"))
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
