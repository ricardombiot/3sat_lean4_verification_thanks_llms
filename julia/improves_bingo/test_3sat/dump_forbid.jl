# Diferencial Lean ↔ Julia del modo FORBID (30-sept-2026, rama reader-stuck; docs/plans/lean_forbid_on.md, F2).
#
#   test_3sat/run_capped.sh 4000 600 julia --heap-size-hint=3G --project=. test_3sat/dump_forbid.jl \
#       <instancia.cnf> <off|on> <salida.txt>
#
# Corre la máquina con el mapa bin y FORBID dado, y vuelca la línea final en el formato de dump_final.jl (sin
# soluciones) más, por gpath, una línea por arista con tríos prohibidos:
#   forbid <a>|<b> r1,r2,…     (a < b por clave; r ∈ forbid(a–b))
# El volcado de Lean (`lake exe bingo-dump SALIDA f.cnf on`) tiene el mismo formato: se comparan con diff.

const PATH = abspath(ARGS[1])
const MODE = Symbol(ARGS[2])
const OUT = abspath(ARGS[3])
include(joinpath(@__DIR__, "..", "src/main.jl"))
const PG = PathOwnersGraph

key(id) = Alias.as_key(id)
keys_sorted(ids) = join(sort(unique([key(id) for id in ids])), ",")

function dump_gpath(io, gpath)
    nodes = []
    PathCollectionLines.for_each(gpath.table_lines, n -> push!(nodes, n))
    sort!(nodes, by = n -> key(n.id))
    println(io, "gpath ", key(gpath.map_parent_id), " step=", gpath.current_step, " valid=", gpath.is_valid)
    println(io, "  nodes ", keys_sorted(n.id for n in nodes))
    println(io, "  global ", keys_sorted(GraphPath.alive_ids(gpath)))
    for n in nodes
        println(io, "  node ", key(n.id))
        println(io, "    owners ", keys_sorted([w for (_, ws) in something(GraphPath.owners_table(gpath, n.id), Dict()) for w in ws]))
        println(io, "    parents ", keys_sorted(n.parents))
        println(io, "    sons ", keys_sorted(n.sons))
    end
    lines = String[]
    for e in values(gpath.og.edges)
        isempty(e.forbid) && continue
        a, b = sort([key(e.a), key(e.b)])
        push!(lines, "  forbid $a|$b $(keys_sorted(collect(e.forbid)))")
    end
    foreach(l -> println(io, l), sort(lines))
end

PG.FORBID[] = MODE
machine = SatMachine.new(GraphMapBin.load_import_bin!(PATH))
redirect_stdout(devnull) do
    SatMachine.run!(machine)
end
PG.FORBID[] = :off
open(OUT, "w") do io
    println(io, "instance ", basename(PATH))
    println(io, "sat ", SatMachine.have_solution(machine))
    gpaths = sort(SatMachine.get_gpath_list(machine), by = g -> key(g.map_parent_id))
    foreach(g -> dump_gpath(io, g), gpaths)
end
