# ¿Qué operación de la máquina conserva SecPair y cuál la necesita del review? (28-sept-2026)
#
#   julia --project=. test_3sat/probe_secpair_ops.jl <salida.tsv>
#
# Cada envío a un destino hace: filter!(requires) (con review) → add_row! → review del UP (solo si add_row! o el
# salto de ventana dejan review_owners) → join en la línea (sin review). Se redefine GraphPath.do_up_filtering!
# (mismo código) para mirar SecPair (by = :map), SecPairX (by = :node) y el cierre por parejas en:
#   S  — tras la selección (filter_require! de cada requisito) y ANTES de su review
#   F  — tras filter!(requires) con su review, antes de add_row!
#   A  — tras add_row! y avanzar el paso, ANTES del review del UP (rev = cuántas veces el review va a correr)
#   U  — tras el review del UP (el gpath que se envía)
# (La línea tras los joins ya está medida en probe_secpair_machine.jl: 0 fallos.)
# Por instancia y punto: n (gpaths válidos), sp, spx, pc (fallos de SecPair, SecPairX, cierre por parejas).

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
include(joinpath(ROOT, "src/main.jl"))

# PROBE_MAP=bin: el mapa bin (el del modelo Lean, con ventanas prohibidas); por defecto, el clásico.
const LOAD = get(ENV, "PROBE_MAP", "classic") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

const PTS = (:S, :F, :A, :U)
const ACC = Dict{Symbol, Vector{Int}}(p => zeros(Int, 4) for p in PTS)
const REV = Ref(0)

function look!(p, g)
    g.is_valid || return
    a = ACC[p]
    a[1] += 1
    isempty(GraphPath.sec_pair_bad(g.og; by = :map)) || (a[2] += 1)
    isempty(GraphPath.sec_pair_bad(g.og; by = :node)) || (a[3] += 1)
    GraphPath.pair_closed(g) || (a[4] += 1)
end

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        for r in requires
            filter_require!(gpath, r)
        end
        $(look!)(:S, gpath)
        make_review_owners!(gpath)
        $(look!)(:F, gpath)
        if gpath.is_valid
            add_row!(gpath, map_id_node, title, prohibited)
            if gpath.is_valid
                gpath.current_step += 1
                gpath.map_parent_id = map_id_node
                $(look!)(:A, gpath)
                gpath.review_owners && ($(REV)[] += 1)
                make_review_owners!(gpath)
                $(look!)(:U, gpath)
            end
        end
    end
end)

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances"),
            joinpath(ROOT, "../../lean/improves_bin/cnf/crafted")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && f != "tseitin_petersen_H.cnf" && push!(files, joinpath(d, f))
        end
    end
    return files
end

function main()
    open(OUT, "w") do io
        println(io, "instance\t" * join(["$(p)_$(c)" for p in PTS for c in ("n", "sp", "spx", "pc")], "\t") * "\trev")
        for path in corpus()
            name = basename(path)
            for p in PTS; fill!(ACC[p], 0); end
            REV[] = 0
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(ACC[p][i]) for p in PTS for i in 1:4], "\t") * "\t$(REV[])")
            flush(io)
        end
    end
end

main()
