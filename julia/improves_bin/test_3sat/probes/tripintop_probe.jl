# TriPin con un nodo de la cima como tercer miembro (docs/context/escalera_reader.md §4.2λ): en un estado de línea g con cima
# `top`, para w en la cima y y, v que poseen w con y que posee v: en cada paso hay una entrada común a y, v y w.
# Si vale, restrictPin g w es un kernel (KernelSplit.restrict_kernel) y la regla del filtro con ancla (AF) sale sola.
#   julia --project=../.. tripintop_probe.jl f1.cnf ...
include("./../../src/main.jl")
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            U = tables(g)
            for w in keys(U)
                w.id.step == top || continue
                S = [y for y in keys(U) if owns(U, y, w)]
                for y in S, v in S
                    y == v && continue
                    owns(U, y, v) || continue
                    for l in 0:top
                        ok = any(e -> e.id.step == l && e in U[v] && e in U[w], U[y])
                        bump(ok ? "TPtop ok" : "TPtop FALLA")
                        ok || get(st, "ej", 0) >= 5 || (bump("ej"); println("TPtop: $(basename(path)) paso $top w=$w y=$y v=$v l=$l"))
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
