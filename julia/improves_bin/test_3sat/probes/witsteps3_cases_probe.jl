# Línea de investigación (docs/context/escalera_reader.md §4.2μ): ¿qué testigos bastan para que una clique tenga cadena?
# En cada estado de línea y en la unión de la línea (sin filtro): Q clique de 3 nodos (muestreo, NS por objeto) con
# testigos solo en los pasos W (con 1–2 nodos la regla de parejas ya da testigos: la pregunta es vacía)
# ⇒ ¿hay cadena por Q? W ∈ {∅, variables, cláusula (L1 L2 L3), solo L3, todos}. Una W sin fallos marca qué testigos
# llevan la información semántica.
#   julia --project=../.. witsteps_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(47)
const NS = parse(Int, get(ENV, "NS", "300"))
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
function probe(path, st)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    kind(l) = l == 0 ? :raiz : l <= 2nv ? :var : l == 2nv + 1 ? :mid : ((l - (2nv + 2)) % 3 == 2 ? :L3 : :L12)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        Ts = Any[]
        CollectionTimeline.for_each_gpath(m.timeline, top, g -> g.is_valid && push!(Ts, tables(g)))
        objs = [(t, "estado") for t in Ts]
        if length(Ts) >= 2
            U = Dict{PathNodeId, Set{PathNodeId}}()
            for T in Ts, (r, S) in T; union!(get!(U, r, Set{PathNodeId}()), S); end
            push!(objs, (U, "unión"))
        end
        Ws = [("∅", l -> false), ("var", l -> kind(l) in (:raiz, :var, :mid)), ("cláusula", l -> kind(l) in (:L12, :L3)),
              ("L3", l -> kind(l) == :L3), ("todos", l -> true)]
        for (T, where) in objs
            B = bystep_of(T); ns = collect(keys(T))
            Qs = Vector{Vector{PathNodeId}}()
            pairs = [(ns[i], ns[k]) for i in eachindex(ns) for k in i+1:length(ns)
                     if ns[i].id.step != ns[k].id.step && owns(T, ns[i], ns[k])]
            for _ in 1:(20 * NS)
                length(Qs) >= NS && break
                isempty(pairs) && break
                (a, b) = rand(pairs)
                cs = [x for x in ns if x.id.step != a.id.step && x.id.step != b.id.step && owns(T, a, x) && owns(T, b, x)]
                isempty(cs) && continue
                push!(Qs, [a, b, rand(cs)])
            end
            unique!(q -> Set(q), Qs)
            for Q in Qs
                isclique(T, Q) || continue
                inC(l) = kind(l) in (:L12, :L3)
                all(l -> !inC(l) || wit(T, B, Q, l), 0:top) || continue
                chain(T, B, Dict(q.id.step => [q] for q in Q), top) && continue
                miss = [l for l in 0:top if !wit(T, B, Q, l)]
                bump("caso")
                println("$(basename(path)) paso $top $where Q=$(map(q -> (q.id.step, q.id.index, q.parent_id, q.gparent_id), Q)) faltan=$(map(l -> (l, kind(l)), miss))")
            end
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
