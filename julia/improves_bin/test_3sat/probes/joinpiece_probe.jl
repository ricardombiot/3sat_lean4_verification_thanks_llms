# ¿Qué pieza elige JoinChoiceP? (docs/context/escalera_reader.md §4.2ξ). Estado unido J, P clique (1 a 3 nodos), enlace y–w con
# CxP_J(y, w). La pieza de un testigo puro del enlace (en el paso n de las claves o en la cima n+1: esos nodos vienen de
# una sola pieza): ¿sirve siempre (∀ testigo puro) o alguno (∃)? Pieza buena = P clique, y, w poseen P y CxP en ella.
#   julia --project=../.. joinpiece_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(79)
const NX = parse(Int, get(ENV, "NX", "10"))
const NP = parse(Int, get(ENV, "NP", "20"))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> haskey(U, q) && all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
ownsall(U, y, P) = haskey(U, y) && all(p -> owns(U, y, p), P)
cxp(U, B, P, y, w, top) = owns(U, y, w) && haskey(U, w) &&
    all(l -> any(r -> owns(U, y, r) && owns(U, w, r) && ownsall(U, r, P), get(B, l, PathNodeId[])), 0:top)
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
                p.is_valid && push!(get!(pieces, d, Any[]), (g.map_parent_id, tables(p)))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            KT = get(pieces, g.map_parent_id, Any[])
            length(KT) >= 2 || return
            Ks = [kt[1] for kt in KT]; Ts = [kt[2] for kt in KT]
            U = tables(g); B = bystep_of(U); ns = collect(keys(U))
            Bs = [bystep_of(T) for T in Ts]
            Ps = Vector{Vector{PathNodeId}}()
            for size in 1:3
                for _ in 1:(20 * NX)
                    count(p -> length(p) == size, Ps) >= NX && break
                    P = [rand(ns)]; ok = true
                    while length(P) < size
                        cs = [x for x in ns if all(q -> q.id.step != x.id.step && owns(U, q, x), P)]
                        isempty(cs) && (ok = false; break)
                        push!(P, rand(cs))
                    end
                    ok && push!(Ps, P)
                end
            end
            for P in Ps
                isclique(U, P) || continue
                NP_ = [y for y in ns if ownsall(U, y, P)]
                prs = [(y, w) for y in NP_ for w in NP_ if y != w && owns(U, y, w)]
                for (y, w) in (length(prs) <= NP ? prs : rand(prs, NP))
                    cxp(U, B, P, y, w, top) || continue
                    goodp(i) = isclique(Ts[i], P) && ownsall(Ts[i], y, P) && ownsall(Ts[i], w, P) && cxp(Ts[i], Bs[i], P, y, w, top)
                    # piece of a pure node: at step n (= top-1) its id is the key; at the top, its parent id is the key
                    pieceof(r) = r.id.step == top - 1 ? findfirst(==(r.id), Ks) : (r.parent_id === nothing ? nothing : findfirst(==(r.parent_id), Ks))
                    for (lname, l) in (("paso n", top - 1), ("cima", top))
                        ws = [r for r in get(B, l, PathNodeId[]) if owns(U, y, r) && owns(U, w, r) && ownsall(U, r, P)]
                        idx = [pieceof(r) for r in ws]
                        any(isnothing, idx) && (bump("sin pieza"); continue)
                        isempty(idx) && continue
                        bump("$lname ∀ testigo puro $(all(goodp, idx) ? "ok" : "FALLA")")
                        bump("$lname ∃ testigo puro $(any(goodp, idx) ? "ok" : "FALLA")")
                    end
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
