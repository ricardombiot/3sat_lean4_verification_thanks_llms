# PieceLocalF: estado unido J de la línea n+1, filtro arbitrario R. Q clique con testigos en filterAll J R ⇒
# ∃ pieza P_i con Q clique con testigos en filterAll P_i R. (Sustituye a PieceLocal, falso con R en el paso n.)
#   Filtros: todos los de un nodo de mapa presente en J y NR al azar de 2–4 nodos.
#   julia --project=../.. djf_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(11)
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
function filt(g, ps)
    p = deepcopy(g)
    redirect_stdout(devnull) do; GraphPath.filter!(p, Set(ps)); end
    p.is_valid ? tables(p) : nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(get!(pieces, d, Any[]), (g.map_parent_id, p))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            g.is_valid || return
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            ids = unique([r.id for r in keys(tables(g))])
            filters = vcat([NodeId[]], [[x] for x in ids], [unique(rand(ids, rand(2:4))) for _ in 1:NR])
            for R in filters
                U = filt(g, R); U === nothing && continue
                B = bystep_of(U)
                Tp = [filt(p, R) for (_, p) in ps]
                Bp = [T === nothing ? nothing : bystep_of(T) for T in Tp]
                ns = collect(keys(U)); Qs = [[x] for x in ns]
                for i in eachindex(ns), k in i+1:length(ns)
                    ns[i].id.step == ns[k].id.step && continue
                    owns(U, ns[i], ns[k]) && push!(Qs, [ns[i], ns[k]])
                end
                tag = isempty(R) ? "DJF R=∅" : length(R) == 1 ? "DJF R=1" : "DJF R=k"
                for Q in Qs
                    good(U, B, Q, s1) || continue
                    ok = any(i -> Tp[i] !== nothing && good(Tp[i], Bp[i], Q, s1), eachindex(ps))
                    bump(ok ? "$tag ok" : "$tag FALLA")
                    ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("$tag: $(basename(path)) paso $s1 R=$R Q=$Q"))
                end
            end
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
