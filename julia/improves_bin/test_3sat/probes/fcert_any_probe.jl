# CertClique con filtros arbitrarios (invariante candidato FC: ∀ ps, CertClique (filterAll g ps)).
#   Para cada estado de línea g: todos los filtros de un nodo de mapa presente en g, y NR filtros al azar de 2–4 nodos.
#   Tras filter! (requisitos + review), si queda válido: toda Q (1 o 2 nodos) clique con testigos ⇒ cadena por Q.
#   julia --project=../.. fcert_any_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(7)
const NR = parse(Int, get(ENV, "NR", "10"))
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
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function chain(U, B, fixed, top)
    sel = Dict{Int, PathNodeId}()
    function go(l)
        l < 0 && return true
        for c in (haskey(fixed, l) ? fixed[l] : get(B, l, PathNodeId[]))
            haskey(U, c) || continue
            all(p -> owns(U, c, p) && owns(U, p, c), values(sel)) || continue
            sel[l] = c
            go(l - 1) && return true
            delete!(sel, l)
        end
        false
    end
    go(top)
end
function check(U, top, tag, st, name)
    B = bystep_of(U); ns = collect(keys(U)); Qs = [[x] for x in ns]
    for i in eachindex(ns), k in i+1:length(ns)
        ns[i].id.step == ns[k].id.step && continue
        owns(U, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
    end
    for Q in Qs
        good(U, B, Q, top) || continue
        ok = chain(U, B, Dict(q.id.step => [q] for q in Q), top)
        k = "$tag $(ok ? "ok" : "FALLA")"; st[k] = get(st, k, 0) + 1
        ok || get(st, "ej $tag", 0) >= 5 || (st["ej $tag"] = get(st, "ej $tag", 0) + 1; println("$tag sin cadena: $name Q=$Q"))
    end
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            U0 = tables(g)
            ids = unique([r.id for r in keys(U0)])
            filters = [[x] for x in ids]
            for _ in 1:NR
                push!(filters, unique(rand(ids, rand(2:4))))
            end
            for ps in filters
                p = deepcopy(g)
                redirect_stdout(devnull) do; GraphPath.filter!(p, Set(ps)); end
                st["filtros"] = get(st, "filtros", 0) + 1
                p.is_valid || (st["filtros inválidos"] = get(st, "filtros inválidos", 0) + 1; continue)
                check(tables(p), s, length(ps) == 1 ? "FC1" : "FCk", st, "$(basename(path)) paso $s ps=$ps")
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
