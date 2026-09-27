# CliqueTri (TriP relativo a una clique, docs/context/ambfar.md §4.2d) con la review corregida, en estados de línea y en los
# estados de partida del lector. P = clique de 3 y de 4 nodos con testigos (muestreo NX por estado y tamaño).
# N_P = nodos que poseen todo P. CxP(y, w): y posee w y en cada paso hay un nodo que posee y, w y todo P.
#   TRIP: y, w ∈ N_P con CxP(y, w) ⇒ en cada paso ∃ r ∈ N_P con CxP(r, y) y CxP(r, w).
# Aquí en los pasos intermedios: (c) la fuente filtrada por los requisitos de cada destino, (a) la pieza (UP, con review si
# salta ventana). Cliques de 1 a 3 nodos.
#   julia --project=../.. cliquetri_ops_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(73)
const NX = parse(Int, get(ENV, "NX", "8"))
const NP = parse(Int, get(ENV, "NP", "30"))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        final = SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m)
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g0)
            g0.is_valid || return
            objs = Any[]
            node = SatMachine.map_get_node(gmap, g0.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                f = deepcopy(g0)
                redirect_stdout(devnull) do; GraphPath.filter!(f, Set(dn.requires)); end
                f.is_valid && push!(objs, (f, "fuente filtrada", top))
                p = deepcopy(g0)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(objs, (p, "pieza", top + 1))
            end
            for (g, donde, top) in objs
            U = tables(g); B = bystep_of(U); ns = collect(keys(U))
            Ps = Vector{Vector{PathNodeId}}()
            for size in (1, 2, 3)
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
            wit(Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
            for P in Ps
                all(l -> wit(P, l), 0:top) || continue
                NP_ = [y for y in ns if all(p -> owns(U, y, p), P)]
                cxc = Dict{Tuple{PathNodeId, PathNodeId}, Bool}()
                CxP(y, w) = get!(cxc, (y, w)) do
                    owns(U, y, w) && all(l -> any(r -> owns(U, r, y) && owns(U, r, w) && all(p -> owns(U, r, p), P),
                                                  get(B, l, PathNodeId[])), 0:top)
                end
                NPB = Dict{Int, Vector{PathNodeId}}()
                for r in NP_; push!(get!(NPB, r.id.step, PathNodeId[]), r); end
                pairs = [(y, w) for y in NP_ for w in NP_ if y != w && owns(U, y, w)]
                for (y, w) in (length(pairs) <= NP ? pairs : rand(pairs, NP))
                    CxP(y, w) || continue
                    ok = all(l -> any(r -> CxP(r, y) && CxP(r, w), get(NPB, l, PathNodeId[])), 0:top)
                    bump("$donde tamaño $(length(P)) TRIP $(ok ? "ok" : "FALLA")")
                    ok || get(st, "ej", 0) >= 4 || (bump("ej"); println("TRIP: $(basename(path)) paso $top $donde P=$P y=$y w=$w"))
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
