# Paso 4 del plan del v181, §6: comparación diferencial del cleanInvalid secuencial y en dos fases.
#
# Para cada instancia y cada modo: veredicto de la máquina, soluciones del lector exponencial
# comprobadas con CheckerCnf, verdad del solver exhaustivo, estados de la línea final (como
# conjuntos: nodos, global, y tabla, padres e hijos de cada nodo), vueltas del review y tiempo.
#
#   julia --project=.. compare_clean.jl

include("./../src/main.jl")

const ROOT = @__DIR__

function corpus()
    dirs = [joinpath(ROOT, "../test/example_cnf"), joinpath(ROOT, "../test_window/instances"),
            joinpath(ROOT, "output/instances"), joinpath(ROOT, "output_test1/instances"),
            joinpath(ROOT, "output_test2/instances"), joinpath(ROOT, "output_test3/instances")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && push!(files, joinpath(d, f))
        end
    end
    return files
end

function truth(path)
    ex = replace(replace(path, "/instances/" => "/solver_exhaustive/"), ".cnf" => ".txt")
    if isfile(ex)
        return strip(first(readlines(ex))) == "SAT"
    end
    try
        solver = ExhaustiveSolver.new(path)
        ExhaustiveSolver.run!(solver)
        return !isempty(solver.list_solutions)
    catch
        return nothing   # el exhaustivo solo acepta 3-SAT estricto
    end
end

owner_entries(owners) = [id for (step, set) in owners.table for id in set]

function signature(gpath)
    nodes = []
    PathCollectionLines.for_each(gpath.table_lines, n -> push!(nodes, n))
    return (Set(n.id for n in nodes), Set(owner_entries(gpath.owners)),
            Dict(n.id => (Set(owner_entries(n.owners)), Set(n.parents), Set(n.sons)) for n in nodes))
end

function run_mode(path, mode)
    GraphPath.CLEAN_MODE[] = mode
    GraphPath.REVIEW_ROUNDS[] = 0
    gmap = GraphMap.load_import!(path)
    machine = SatMachine.new(gmap)
    t = @elapsed SatMachine.run!(machine)
    sat = SatMachine.have_solution(machine)
    sigs = Dict(gp.map_parent_id => signature(gp) for gp in SatMachine.get_gpath_list(machine))
    sols_ok = true
    nsols = 0
    if sat
        gpath = first(SatMachine.get_gpath_solutions(machine))
        reader = PathExpReader.new(gpath)
        PathExpReader.read!(reader)
        nsols = length(reader.list_solutions)
        sols_ok = nsols > 0 && CheckerCnf.test_all(reader.list_solutions, path)
    end
    return (sat = sat, t = t, rounds = GraphPath.REVIEW_ROUNDS[], sigs = sigs,
            sols_ok = sols_ok, nsols = nsols)
end

function main()
    files = corpus()
    n = 0; same_verdict = 0; right = 0; same_states = 0; sols_bad = 0; skipped = 0; notruth = 0
    t_seq = 0.0; t_two = 0.0; r_seq = 0; r_two = 0
    for path in files
        tr = truth(path)
        local a, b
        try
            a = run_mode(path, :sequential)
            b = run_mode(path, :two_phase)
        catch e
            skipped += 1
            println("$(basename(path)): SALTADA ($(typeof(e)))")
            continue
        end
        n += 1
        same_verdict += (a.sat == b.sat)
        if tr === nothing
            notruth += 1
        else
            right += (a.sat == tr && b.sat == tr)
        end
        st = a.sigs == b.sigs
        same_states += st
        sols_bad += (!a.sols_ok || !b.sols_ok)
        t_seq += a.t; t_two += b.t; r_seq += a.rounds; r_two += b.rounds
        println("$(basename(path)): verdad=$(tr === nothing ? "?" : (tr ? "SAT" : "UNSAT")) seq=$(a.sat) dos=$(b.sat) " *
                "estados=$(st ? "iguales" : "DISTINTOS") soluciones=$(a.sols_ok && b.sols_ok ? "ok" : "MAL") " *
                "vueltas $(a.rounds)/$(b.rounds) tiempo $(round(a.t, digits=2))/$(round(b.t, digits=2))s")
    end
    println("── $n instancias ($skipped saltadas, $notruth sin verdad del exhaustivo)")
    println("   mismo veredicto: $same_verdict   ambos aciertan la verdad: $right   estados finales iguales: $same_states")
    println("   soluciones leidas que fallan el checker (algun modo): $sols_bad")
    println("   vueltas del review secuencial/dos fases: $r_seq / $r_two   tiempo: $(round(t_seq, digits=1)) / $(round(t_two, digits=1)) s")
end

main()
