# Pasos A0 y A4 del plan docs/plans/pair_mode.md: comparación diferencial del review sin la regla de
# parejas (PAIR_MODE :off) y con ella (:on). Misma estructura que compare_sym.jl.
#
# Para cada instancia y cada modo:
#   * la máquina: veredicto, estados de la línea final (como conjuntos), vueltas del review, tiempo;
#   * el lector sin retroceso (PathReader) sobre la línea final: su asignación y el checker, y la
#     firma del estado tras cada pin;
#   * el lector exponencial: el conjunto de soluciones leídas, comprobadas con CheckerCnf.
# Contadores por fase (máquina / lectores): PAIR_REMOVED, PAIR_ROUNDS, PAIR_MAXSTEP y la rama
# «inconsistente» del filtro agresivo (AGG_INCONS). Las columnas :off de AGG_INCONS son la base de A0.
#
#   julia --project=.. compare_pair.jl

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

const COUNTERS = (:removed => GraphPath.PAIR_REMOVED, :rounds => GraphPath.PAIR_ROUNDS,
                  :maxstep => GraphPath.PAIR_MAXSTEP, :incons => GraphPath.AGG_INCONS)
reset_counters!() = foreach(c -> c.second[] = 0, COUNTERS)
read_counters() = Dict(c.first => c.second[] for c in COUNTERS)

# El lector sin retroceso, paso a paso, guardando la firma tras cada pin.
function read_plain(gpath)
    reader = PathReader.new(deepcopy(gpath))
    sigs = []
    ok = true
    try
        redirect_stdout(devnull) do
            while !reader.is_finished
                PathReader.read_step!(reader)
                push!(sigs, signature(reader.gpath))
            end
        end
    catch
        ok = false
    end
    return (ok = ok, solution = reader.solution, sigs = sigs)
end

function run_mode(path, mode)
    GraphPath.PAIR_MODE[] = mode
    GraphPath.REVIEW_ROUNDS[] = 0
    reset_counters!()
    machine = SatMachine.new(GraphMap.load_import!(path))
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    c_machine = read_counters()
    rounds = GraphPath.REVIEW_ROUNDS[]
    sat = SatMachine.have_solution(machine)
    sigs = Dict(gp.map_parent_id => signature(gp) for gp in SatMachine.get_gpath_list(machine))

    reset_counters!()
    plain = (ok = true, solution = BitVector(), sigs = [])
    plain_check = true
    sols = Set{BitVector}()
    sols_ok = true
    t_read = 0.0
    if sat
        gpath = first(SatMachine.get_gpath_solutions(machine))
        t_read = @elapsed begin
            plain = read_plain(gpath)
            reader = PathExpReader.new(deepcopy(gpath))
            redirect_stdout(devnull) do
                PathExpReader.read!(reader)
            end
        end
        plain_check = plain.ok && CheckerCnf.test_all([plain.solution], path)
        sols = Set(BitVector(s) for s in reader.list_solutions)
        sols_ok = !isempty(sols) && CheckerCnf.test_all(collect(sols), path)
    end
    c_reader = read_counters()
    return (sat = sat, t = t, t_read = t_read, rounds = rounds, sigs = sigs, plain = plain,
            plain_check = plain_check, sols = sols, sols_ok = sols_ok, cm = c_machine, cr = c_reader)
end

function main()
    files = corpus()
    n = 0; skipped = 0; notruth = 0
    same_verdict = 0; right = 0; same_states = 0; same_plain = 0; same_plain_sigs = 0; same_sols = 0
    bad_check = 0
    t_off = 0.0; t_on = 0.0; tr_off = 0.0; tr_on = 0.0; r_off = 0; r_on = 0
    tot = Dict((m, ph, k) => 0 for m in (:off, :on), ph in (:m, :r), k in first.(COUNTERS))
    fired_reader = 0
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
        tr === nothing ? (notruth += 1) : (right += (a.sat == tr && b.sat == tr))
        st = a.sigs == b.sigs; same_states += st
        sp = a.plain.solution == b.plain.solution; same_plain += sp
        ss = a.plain.sigs == b.plain.sigs; same_plain_sigs += ss
        so = a.sols == b.sols; same_sols += so
        bad_check += !(a.plain_check && b.plain_check && a.sols_ok && b.sols_ok)
        t_off += a.t; t_on += b.t; tr_off += a.t_read; tr_on += b.t_read; r_off += a.rounds; r_on += b.rounds
        for (m, x) in ((:off, a), (:on, b)), k in first.(COUNTERS)
            tot[(m, :m, k)] += x.cm[k]; tot[(m, :r, k)] += x.cr[k]
        end
        fired_reader += b.cr[:removed] > 0
        println("$(basename(path)): verdad=$(tr === nothing ? "?" : (tr ? "SAT" : "UNSAT")) off=$(a.sat) on=$(b.sat) " *
                "estados=$(st ? "iguales" : "DISTINTOS") lector=$(sp ? "igual" : "DISTINTO")/$(ss ? "pines iguales" : "PINES DISTINTOS") " *
                "exp=$(so ? "iguales" : "DISTINTAS")($(length(a.sols))/$(length(b.sols))) " *
                "checker=$(a.plain_check && b.plain_check && a.sols_ok && b.sols_ok ? "ok" : "MAL") " *
                "vueltas $(a.rounds)/$(b.rounds) regla maq/lect $(b.cm[:removed])/$(b.cr[:removed]) " *
                "incons maq off/on $(a.cm[:incons])/$(b.cm[:incons]) lect off/on $(a.cr[:incons])/$(b.cr[:incons]) " *
                "tiempo $(round(a.t + a.t_read, digits=2))/$(round(b.t + b.t_read, digits=2))s")
    end
    println("── $n instancias ($skipped saltadas, $notruth sin verdad del exhaustivo)")
    println("   mismo veredicto: $same_verdict   ambos aciertan la verdad: $right   estados finales iguales: $same_states")
    println("   lector sin retroceso: misma asignación $same_plain, mismos estados tras cada pin $same_plain_sigs")
    println("   lector exponencial: mismas soluciones $same_sols   instancias con algún fallo del checker: $bad_check")
    println("   vueltas del review de la máquina off/on: $r_off / $r_on")
    println("   tiempo máquina off/on: $(round(t_off, digits=1)) / $(round(t_on, digits=1)) s   lectores off/on: $(round(tr_off, digits=1)) / $(round(tr_on, digits=1)) s")
    for ph in (:m, :r)
        name = ph == :m ? "máquina" : "lectores"
        println("   $name: rama inconsistente del agresivo off/on $(tot[(:off, ph, :incons)]) / $(tot[(:on, ph, :incons)])   " *
                "regla (on): parejas quitadas $(tot[(:on, ph, :removed)]), vueltas $(tot[(:on, ph, :rounds)]), max_step distinto $(tot[(:on, ph, :maxstep)])")
    end
    println("   instancias en que la regla actúa en los lectores: $fired_reader")
end

main()
