# TriPin y TriPin₁ (docs/context/ambfar.md §4.2b, OneShot) con la review corregida, en estados de línea.
# Para x (muestreo NX por estado): N_x = nodos que poseen x. Cx(y, w): y posee w y en cada paso hay un nodo que posee y, w, x.
#   TP:  y, w ∈ N_x, y posee w ⇒ en cada paso ∃ r que posee y, w, x.
#   TP1: y, w ∈ N_x con Cx(y, w) ⇒ en cada paso ∃ r ∈ N_x con Cx(r, y) y Cx(r, w).
# Muestreo NP parejas por x. Clasifica por la posición de x (top de la línea o no).
#   julia --project=../.. tripin1_probe.jl f1.cnf ...
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
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            U = tables(g); B = bystep_of(U); ns = collect(keys(U))
            for x in (length(ns) <= NX ? ns : rand(ns, NX))
                Nx = [y for y in ns if owns(U, y, x)]
                cxc = Dict{Tuple{PathNodeId, PathNodeId}, Bool}()
                Cx(y, w) = get!(cxc, (y, w)) do
                    owns(U, y, w) && all(l -> any(r -> owns(U, r, y) && owns(U, r, w) && owns(U, r, x), get(B, l, PathNodeId[])), 0:top)
                end
                pairs = [(y, w) for y in Nx for w in Nx if y != w && owns(U, y, w)]
                isempty(pairs) && continue
                where = x.id.step == top ? "x en la cima" : "x abajo"
                for (y, w) in (length(pairs) <= NP ? pairs : rand(pairs, NP))
                    tp = all(l -> any(r -> owns(U, r, y) && owns(U, r, w) && owns(U, r, x), get(B, l, PathNodeId[])), 0:top)
                    bump("TP $(tp ? "ok" : "FALLA")"); tp || bump("TP FALLA $where")
                    Cx(y, w) || continue
                    NxB = Dict{Int, Vector{PathNodeId}}()
                    for r in Nx; push!(get!(NxB, r.id.step, PathNodeId[]), r); end
                    tp1 = all(l -> any(r -> Cx(r, y) && Cx(r, w), get(NxB, l, PathNodeId[])), 0:top)
                    bump("TP1 $(tp1 ? "ok" : "FALLA")"); tp1 || bump("TP1 FALLA $where")
                    tp1 || get(st, "ej", 0) >= 4 || (bump("ej"); println("TP1: $(basename(path)) paso $top x=$x y=$y w=$w"))
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
