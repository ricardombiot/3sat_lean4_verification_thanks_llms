# Paso A0 del plan docs/plans/review_simetrico.md: medir la asimetría de las tablas en la máquina
# actual, sin cambiarla.
#
# Se redefinen (solo en este proceso) make_review_owners! y do_up_filtering! con el mismo código más
# contadores. Una pareja asimétrica viva: x y w nodos vivos, w ∈ owners(x), x ∉ owners(w).
# Se cuenta tras cada etapa del review, a la entrada de cada envío (línea recibida, tras la unión) y
# tras UP (la fila nueva). Y, aparte, en los estados del lector (línea final pinchada y revisada).
#
#   julia --project=.. measure_symmetry.jl [test_window|all]

include("./../src/main.jl")

const ROOT = @__DIR__

function corpus(which)
    dirs = [joinpath(ROOT, "../test_window/instances")]
    if which == "all"
        append!(dirs, [joinpath(ROOT, "../test/example_cnf"), joinpath(ROOT, "output/instances"),
                       joinpath(ROOT, "output_test1/instances"), joinpath(ROOT, "output_test2/instances"),
                       joinpath(ROOT, "output_test3/instances")])
    end
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && push!(files, joinpath(d, f))
        end
    end
    return files
end

function all_nodes(gpath)
    nodes = []
    PathCollectionLines.for_each(gpath.table_lines, n -> push!(nodes, n))
    return nodes
end

# Parejas asimétricas entre nodos vivos (cada dirección que falta cuenta una vez).
function asym_pairs(gpath)
    n = 0
    for x in all_nodes(gpath)
        for (step, set) in x.owners.table
            for wid in set
                wid == x.id && continue
                w = PathCollectionLines.get_node(gpath.table_lines, wid)
                w === nothing && continue
                n += !PathDocumentOwners.is_owner(w.owners, x.id)
            end
        end
    end
    return n
end

count_nodes(gpath) = length(all_nodes(gpath))

const STAGES = [:entrada, :clean, :padres, :hijos, :agresivo, :cadena]
mutable struct Acc
    reviews :: Int
    asym_states :: Dict{Symbol,Int}   # estados con alguna asimetría, por etapa
    asym_pairs :: Dict{Symbol,Int}    # parejas asimétricas, por etapa
    removed_padres :: Int             # nodos eliminados en la pasada de padres
    removed_hijos :: Int
    states_removed_pass :: Int        # vueltas en que alguna pasada eliminó nodos
    envios :: Int
    asym_recv :: Int                  # envíos cuya línea recibida es asimétrica
    asym_up :: Int                    # envíos con asimetría justo tras UP (sin review después)
    asym_up_new :: Int                # ... en la que interviene un nodo de la fila nueva
end
Acc() = Acc(0, Dict(s => 0 for s in STAGES), Dict(s => 0 for s in STAGES), 0, 0, 0, 0, 0, 0, 0)
const ACC = Ref(Acc())

function note!(stage, gpath)
    gpath.is_valid || return   # un grafo inválido se descarta: su asimetría no importa
    a = asym_pairs(gpath)
    ACC[].asym_pairs[stage] += a
    ACC[].asym_states[stage] += (a > 0)
end

@eval GraphPath function make_review_owners!(gpath :: GPath)
    acc = Main.ACC[]
    if gpath.is_valid && gpath.review_owners
        REVIEW_ROUNDS[] += 1
        acc.reviews += 1
        Main.note!(:entrada, gpath)
        gpath.review_owners = false
        clean_invalid_nodes!(gpath)
        Main.note!(:clean, gpath)
        n0 = Main.count_nodes(gpath)
        review_owners_parents_sons!(gpath)
        n1 = Main.count_nodes(gpath)
        Main.note!(:padres, gpath)
        review_owners_sons_parents!(gpath)
        n2 = Main.count_nodes(gpath)
        Main.note!(:hijos, gpath)
        acc.removed_padres += n0 - n1
        acc.removed_hijos += n1 - n2
        acc.states_removed_pass += (n2 < n0)
        agressive_consistence_filter!(gpath)
        Main.note!(:agresivo, gpath)
        chain_consistence_filter!(gpath)
        Main.note!(:cadena, gpath)
        if gpath.review_owners
            make_review_owners!(gpath)
        end
    end
end

@eval GraphPath function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String)
    acc = Main.ACC[]
    acc.envios += 1
    acc.asym_recv += (Main.asym_pairs(gpath) > 0)
    filter!(gpath, requires)
    before = gpath.is_valid ? Main.asym_pairs(gpath) : 0
    do_up!(gpath, map_id_node, title)
    after = gpath.is_valid ? Main.asym_pairs(gpath) : 0
    acc.asym_up += (after > 0)
    acc.asym_up_new += (after > before)
end

# Estados del lector: línea final, pin de cada id de mapa de un paso con dos o más, y review.
function reader_states!(machine, acc_reader)
    for gpath in SatMachine.get_gpath_list(machine)
        for step in 0:gpath.current_step-1
            ids = PathCollectionLines.get_ids_step(gpath.table_lines, step)
            map_ids = unique([pid.id for pid in ids])
            length(map_ids) < 2 && continue
            for x in map_ids
                g = deepcopy(gpath)
                GraphPath.filter_require!(g, x)
                GraphPath.make_review_owners!(g)
                acc_reader[1] += 1
                acc_reader[2] += g.is_valid && asym_pairs(g) > 0
            end
        end
    end
end

function report(title, acc)
    println("── $title: $(acc.reviews) vueltas del review, $(acc.envios) envíos")
    for s in STAGES
        println("   tras $(rpad(String(s), 9)): estados con asimetría $(acc.asym_states[s]), parejas $(acc.asym_pairs[s])")
    end
    println("   nodos eliminados en pasadas: padres $(acc.removed_padres), hijos $(acc.removed_hijos); vueltas con alguno $(acc.states_removed_pass)")
    println("   envíos: línea recibida asimétrica $(acc.asym_recv); tras UP asimétrica $(acc.asym_up) (nueva asimetría por la fila nueva $(acc.asym_up_new))")
end

function main()
    which = length(ARGS) >= 1 ? ARGS[1] : "test_window"
    total = Acc()
    reader = [0, 0]
    for path in corpus(which)
        ACC[] = Acc()
        local machine
        try
            gmap = GraphMap.load_import!(path)
            machine = SatMachine.new(gmap)
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        catch e
            println("$(basename(path)): SALTADA ($(typeof(e)))")
            continue
        end
        a = ACC[]
        println("$(basename(path)): vueltas $(a.reviews), asim. tras clean $(a.asym_states[:clean]) padres $(a.asym_states[:padres]) " *
                "hijos $(a.asym_states[:hijos]) agresivo $(a.asym_states[:agresivo]); eliminados en pasadas $(a.removed_padres + a.removed_hijos); " *
                "UP $(a.asym_up)")
        for f in fieldnames(Acc)
            v = getfield(a, f)
            if v isa Dict
                for (k, x) in v; getfield(total, f)[k] += x; end
            else
                setfield!(total, f, getfield(total, f) + v)
            end
        end
        ACC[] = Acc()
        redirect_stdout(devnull) do
            reader_states!(machine, reader)
        end
    end
    report("máquina (envíos)", total)
    println("── lector: $(reader[1]) estados pinchados y revisados, con asimetría $(reader[2])")
end

main()
