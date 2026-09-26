# PieceF, caso con miembro en la cima (docs/context/ambfar.md §4.2κ). Pieza P = upF g d filtrada por ps (∅, un nodo
# de mapa, o 2–4 al azar). Q = w :: Q0 con w en la cima, buena en filterAll P ps:
#   TOPPAR: ∃ padre c de w con Q0 ∪ {c} buena en filterAll P ps (la cadena por c sube a w).
#   FCP:    Q buena ⇒ cadena por Q (CertClique de la pieza filtrada), todas las Q.
#   Cuenta también cuántas cimas tienen dos padres (fusión).
#   julia --project=../.. toppar_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(13)
const NR = parse(Int, get(ENV, "NR", "4"))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}(); P = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
        P[pid_] = Set(node.parents)
    end
    U, P
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
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid || continue
                top = s + 1
                ids = unique([r.id for r in keys(tables(p)[1])])
                for ps in vcat([NodeId[]], [[x] for x in ids], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
                    f = deepcopy(p)
                    redirect_stdout(devnull) do; GraphPath.filter!(f, Set(ps)); end
                    f.is_valid || continue
                    U, Par = tables(f); B = bystep_of(U)
                    tops = get(B, top, PathNodeId[])
                    for w in tops; bump(length(get(Par, w, Set())) >= 2 ? "cimas con fusión" : "cimas sin fusión"); end
                    ns = collect(keys(U)); Qs = [[x] for x in ns]
                    for i in eachindex(ns), k in i+1:length(ns)
                        ns[i].id.step == ns[k].id.step && continue
                        owns(U, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
                    end
                    for Q in Qs
                        good(U, B, Q, top) || continue
                        ok = chain(U, B, Dict(q.id.step => [q] for q in Q), top)
                        bump(ok ? "FCP ok" : "FCP FALLA")
                        iw = findfirst(q -> q.id.step == top, Q)
                        iw === nothing && continue
                        w = Q[iw]; Q0 = [q for q in Q if q != w]
                        pars = collect(get(Par, w, Set()))
                        tag = length(pars) >= 2 ? "TOPPAR fusión" : "TOPPAR simple"
                        okp = any(c -> good(U, B, vcat(Q0, [c]), top), pars)
                        bump(okp ? "$tag ok" : "$tag FALLA")
                        okp || get(st, "ej", 0) >= 5 || (bump("ej"); println("$tag: $(basename(path)) paso $top ps=$ps Q=$Q padres=$pars"))
                    end
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
