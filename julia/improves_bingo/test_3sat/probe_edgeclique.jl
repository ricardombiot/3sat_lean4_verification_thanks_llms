# EdgeClique y ReviewExact (28-sept-2026; plan: invariante de la máquina hacia NoDeadEnd).
#
#   julia --project=. test_3sat/probe_edgeclique.jl <salida.tsv> [tope_cadenas]
#
# EdgeClique g: toda arista y todo nodo vivo de g están en alguna camarilla llevada (Lean `Carried`): una cadena de
# enlaces padre → hijo desde una raíz (paso 0) hasta la cima (current_step - 1), por nodos vivos que se poseen dos a
# dos. Se enumeran todas las cadenas (DFS con poda por posesión, hasta tope_cadenas; si se pasa, el estado cuenta
# como truncado y no se juzga) y se miran las aristas y los nodos que no cubre ninguna.
#
# ReviewExact: tras seleccionar b (filter_require!) y revisar, toda arista está en una camarilla por b. En ese
# estado el paso de b solo tiene vivos de b, así que toda camarilla pasa por b: ReviewExact ⇔ EdgeClique en F.
#
# Puntos (como probe_secpair_ops.jl): F tras la selección con su review, A tras add_row! (sin review), U tras el
# review del UP, L cada gpath de la línea tras los joins. Por instancia y punto: n (estados juzgados), fail (estados
# con algo sin cubrir), e_miss / v_miss (aristas / nodos sin cubrir), trunc (estados truncados).

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const CAP = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20000
include(joinpath(ROOT, "src/main.jl"))

# PROBE_MAP=bin: el mapa bin (el del modelo Lean, con ventanas prohibidas); por defecto, el clásico.
const LOAD = get(ENV, "PROBE_MAP", "classic") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const PTS = (:F, :A, :U, :L)
const ACC = Dict{Symbol, Vector{Int}}(p => zeros(Int, 5) for p in PTS)

# GraphPath.edge_clique_miss (espejo de EdgeClique.lean): (aristas, nodos) sin cubrir, o nothing si se pasa del tope.
coverage(g) = GraphPath.edge_clique_miss(g; cap = CAP)

function look!(p, g)
    g.is_valid || return
    a = ACC[p]
    c = coverage(g)
    if c === nothing
        a[5] += 1
        return
    end
    a[1] += 1
    (c[1] > 0 || c[2] > 0) && (a[2] += 1)
    a[3] += c[1]; a[4] += c[2]
end

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        filter!(gpath, requires)
        $(look!)(:F, gpath)
        if gpath.is_valid
            add_row!(gpath, map_id_node, title, prohibited)
            if gpath.is_valid
                gpath.current_step += 1
                gpath.map_parent_id = map_id_node
                $(look!)(:A, gpath)
                make_review_owners!(gpath)
                $(look!)(:U, gpath)
            end
        end
    end
end)

line(machine) = (gs = GPath[]; CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step,
                                                                  g -> push!(gs, g)); gs)

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
        println(io, "instance\t" * join(["$(p)_$(c)" for p in PTS for c in ("n", "fail", "e_miss", "v_miss", "trunc")], "\t"))
        for path in corpus()
            name = basename(path)
            for p in PTS; fill!(ACC[p], 0); end
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.init!(machine)
                end
                while true
                    foreach(g -> look!(:L, g), line(machine))
                    (!SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)) || break
                    redirect_stdout(devnull) do
                        SatMachine.make_step!(machine)
                    end
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(ACC[p][i]) for p in PTS for i in 1:5], "\t"))
            flush(io)
        end
    end
end

main()
