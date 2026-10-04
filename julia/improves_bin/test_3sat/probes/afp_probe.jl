# AF en las piezas (lean/improves_bin AnchorPiece.AFP). Pieza P = upF g d filtrada por ps (∅, un nodo, NR al azar).
# Q = w (+ q) buena con w en la cima; m un nodo de mapa en un paso ≤ n que w fija (todas sus entradas de ese paso lo
# nombran) ⇒ Q buena en filterAll P (ps ∪ {m}).
#   julia --project=../.. afp_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(31)
const NR = parse(Int, get(ENV, "NR", "2"))
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
function filt(g, R)
    p = deepcopy(g)
    redirect_stdout(devnull) do; GraphPath.filter!(p, Set(R)); end
    p.is_valid ? tables(p) : nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step; top = s + 1
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
                ids = unique([r.id for r in keys(tables(p))])
                for ps in vcat([NodeId[]], [[x] for x in ids], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
                    U = filt(p, ps); U === nothing && continue
                    B = bystep_of(U); cache = Dict{NodeId, Any}()
                    for w in get(B, top, PathNodeId[])
                        fixed = NodeId[]
                        for l in 0:s
                            idsl = unique([v.id for v in U[w] if v.id.step == l])
                            length(idsl) == 1 && push!(fixed, idsl[1])
                        end
                        for Q in vcat([[w]], [[w, q] for q in keys(U) if q.id.step < top && owns(U, w, q)])
                            good(U, B, Q, top) || continue
                            for mid in fixed
                                r = get!(cache, mid) do
                                    T = filt(p, vcat(ps, [mid])); T === nothing ? nothing : (T, bystep_of(T))
                                end
                                ok = r !== nothing && good(r[1], r[2], Q, top)
                                bump(ok ? "AFP ok" : "AFP FALLA")
                                ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("AFP: $(basename(path)) paso $top ps=$ps Q=$Q m=$mid"))
                            end
                        end
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
