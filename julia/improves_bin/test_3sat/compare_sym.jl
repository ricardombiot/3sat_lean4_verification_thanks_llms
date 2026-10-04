# Paso A5 del plan docs/plans/review_simetrico.md: comparación diferencial del review sin espejo
# (SYM_MODE :off) y simétrico (:on). Misma estructura que compare_clean.jl.
#
# Para cada instancia y cada modo: veredicto de la máquina, soluciones del lector exponencial
# comprobadas con CheckerCnf, verdad del solver exhaustivo, estados de la línea final (como
# conjuntos: nodos, global, y tabla, padres e hijos de cada nodo), vueltas del review y tiempo.
#
#   julia --project=.. compare_sym.jl

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
    GraphPath.SYM_MODE[] = mode
    GraphPath.REVIEW_ROUNDS[] = 0
    GraphPath.MIRROR_REMOVED[] = 0
    GraphPath.AGG_ASYM[] = 0
    gmap = GraphMap.load_import!(path)
    machine = SatMachine.new(gmap)
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    mirror = GraphPath.MIRROR_REMOVED[]; agg_asym = GraphPath.AGG_ASYM[]
    sat = SatMachine.have_solution(machine)
    sigs = Dict(gp.map_parent_id => signature(gp) for gp in SatMachine.get_gpath_list(machine))
    sols_ok = true
    nsols = 0
    if sat
        gpath = first(SatMachine.get_gpath_solutions(machine))
        reader = PathExpReader.new(gpath)
        redirect_stdout(devnull) do
            PathExpReader.read!(reader)
        end
        nsols = length(reader.list_solutions)
        sols_ok = nsols > 0 && CheckerCnf.test_all(reader.list_solutions, path)
    end
    return (sat = sat, t = t, rounds = GraphPath.REVIEW_ROUNDS[], sigs = sigs,
            sols_ok = sols_ok, nsols = nsols, mirror = mirror, agg_asym = agg_asym)
end

function main()
    files = corpus()
    n = 0; same_verdict = 0; right = 0; same_states = 0; sols_bad = 0; skipped = 0; notruth = 0
    t_seq = 0.0; t_two = 0.0; r_seq = 0; r_two = 0; mirror = 0; asym_off = 0; asym_on = 0; nsol_off = 0; nsol_on = 0
    for path in files
        tr = truth(path)
        local a, b
        try
            a = run_mode(path, :off)
            b = run_mode(path, :on)
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
        mirror += b.mirror; asym_off += a.agg_asym; asym_on += b.agg_asym; nsol_off += a.nsols; nsol_on += b.nsols
        println("$(basename(path)): verdad=$(tr === nothing ? "?" : (tr ? "SAT" : "UNSAT")) off=$(a.sat) on=$(b.sat) " *
                "estados=$(st ? "iguales" : "DISTINTOS") soluciones=$(a.sols_ok && b.sols_ok ? "ok" : "MAL") " *
                "vueltas $(a.rounds)/$(b.rounds) espejo $(b.mirror) asim.agresivo $(a.agg_asym)/$(b.agg_asym) sols $(a.nsols)/$(b.nsols) tiempo $(round(a.t, digits=2))/$(round(b.t, digits=2))s")
    end
    println("── $n instancias ($skipped saltadas, $notruth sin verdad del exhaustivo)")
    println("   mismo veredicto: $same_verdict   ambos aciertan la verdad: $right   estados finales iguales: $same_states")
    println("   soluciones leidas que fallan el checker (algun modo): $sols_bad")
    println("   vueltas del review off/on: $r_seq / $r_two   tiempo: $(round(t_seq, digits=1)) / $(round(t_two, digits=1)) s")
    println("   entradas espejo borradas (on): $mirror   rama asimetrica del agresivo off/on: $asym_off / $asym_on   soluciones leidas off/on: $nsol_off / $nsol_on")
end

main()
