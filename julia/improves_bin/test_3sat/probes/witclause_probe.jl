# Línea de investigación (docs/context/ambfar.md §4.2μ): ¿qué testigos bastan para que una clique tenga cadena?
# En cada estado de línea y en la unión de la línea (sin filtro): Q clique de 3 nodos (muestreo, NS por objeto) con
# testigos solo en los pasos W (con 1–2 nodos la regla de parejas ya da testigos: la pregunta es vacía).
# Versión local por cláusula: una cláusula TOCA a Q si alguno de sus literales es de una variable con miembro de Q en su
# paso de variable, o si Q tiene un miembro en su bloque. W = pasos de las cláusulas que tocan a Q (+ frontera).
# Y para las cliques sin cadena: ¿cuántas cláusulas sin testigo hay, y tocan a Q?
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
    lines = readlines(path)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), lines)))[3])
    clauses = [filter(!=(0), parse.(Int, split(l))) for l in lines
               if !isempty(strip(l)) && !startswith(l, "c") && !startswith(l, "p") && !startswith(l, "%")]
    clauses = filter(!isempty, clauses)
    cstep(j) = 2nv + 2 + 3(j - 1)
    clauseof(l) = l >= 2nv + 2 ? (l - (2nv + 2)) ÷ 3 + 1 : 0
    varof(l) = (1 <= l <= 2nv) ? (l + 1) ÷ 2 : 0
    touches(j, Q) = any(q -> clauseof(q.id.step) == j, Q) ||
        any(lit -> any(q -> varof(q.id.step) == abs(lit), Q), clauses[j])
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
        front(l) = 2nv - 1 <= l <= 2nv + 1
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
                has = chain(T, B, Dict(q.id.step => [q] for q in Q), top)
                closed = [j for j in eachindex(clauses) if cstep(j) + 2 <= top]
                wj(j) = all(l -> wit(T, B, Q, l), cstep(j):cstep(j)+2)
                # sufficiency of the touching clauses
                if all(j -> !touches(j, Q) || wj(j), closed) && all(l -> !front(l) || l > top || wit(T, B, Q, l), 0:top)
                    bump("$where W=tocan+frontera $(has ? "ok" : "FALLA")")
                end
                if !has
                    missC = [j for j in closed if !wj(j)]
                    bump("$where sin cadena")
                    bump("$where sin cadena: cláusulas sin testigo = $(min(length(missC), 3))$(length(missC) >= 3 ? "+" : "")")
                    bump("$where sin cadena: alguna sin testigo toca a Q = $(any(j -> touches(j, Q), missC))")
                    bump("$where sin cadena: todas las sin testigo tocan a Q = $(all(j -> touches(j, Q), missC))")
                end
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
