# JoinChoiceP (docs/context/escalera_reader.md §4.2ν): estado unido J con ≥ 2 piezas, P clique de J (0 a 3 nodos, muestreo), y, w
# que poseen P en J con CxP_J(y, w) ⇒ ¿hay una pieza X con P clique en X, y, w nodos de X que poseen P en X y CxP_X(y, w)?
# Si vale, CliqueTri de las piezas pasa al estado unido (Lean: JoinTri.cliqueTri_of_joinChoice).
#   julia --project=../.. joinchoicep_probe.jl f1.cnf ...
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
                p.is_valid && push!(get!(pieces, d, Any[]), tables(p))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            Ts = get(pieces, g.map_parent_id, Any[])
            length(Ts) >= 2 || return
            U = tables(g); B = bystep_of(U); ns = collect(keys(U))
            Bs = [bystep_of(T) for T in Ts]
            Ps = Vector{Vector{PathNodeId}}([PathNodeId[]])
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
                    ok = any(i -> isclique(Ts[i], P) && ownsall(Ts[i], y, P) && ownsall(Ts[i], w, P) &&
                                  cxp(Ts[i], Bs[i], P, y, w, top), eachindex(Ts))
                    bump("tamaño $(length(P)) JOINCHOICEP $(ok ? "ok" : "FALLA")")
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
