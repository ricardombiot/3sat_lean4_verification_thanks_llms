# TopMergeJ (lean/improves_bin AnchorPiece.lean): estado de línea g (unidos incluidos) filtrado por R (vacío, de un
# nodo, NR de 2–4 al azar). Q = w :: Q0 buena con w en la cima con dos padres distintos, Q0 por debajo:
#   TMJ: ∃ padre c de w con c :: Q0 buena en el mismo estado filtrado.
#   julia --project=../.. topmergej_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(29)
const NR = parse(Int, get(ENV, "NR", "2"))
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
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            ids = unique([r.id for r in keys(tables(g)[1])])
            for R in vcat([NodeId[]], [[x] for x in ids], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
                f = deepcopy(g)
                redirect_stdout(devnull) do; GraphPath.filter!(f, Set(R)); end
                f.is_valid || continue
                U, Par = tables(f); B = bystep_of(U)
                for w in get(B, top, PathNodeId[])
                    pars = collect(get(Par, w, Set()))
                    length(pars) >= 2 || continue
                    bump("cimas con fusión")
                    for Q0 in vcat([PathNodeId[]], [[q] for q in keys(U) if q.id.step < top && owns(U, w, q)])
                        good(U, B, vcat([w], Q0), top) || continue
                        ok = any(c -> good(U, B, vcat([c], Q0), top), pars)
                        bump(ok ? "TMJ ok" : "TMJ FALLA")
                        ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("TMJ: $(basename(path)) paso $top R=$R w=$w Q0=$Q0 padres=$pars"))
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
