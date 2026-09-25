# Fase D del plan docs/plans/bin-map.md: comparación diferencial del mapa clásico vs el mapa bin.
#
# Para cada instancia, sobre cada mapa:
#   * máquina: veredicto, tiempo, stepCount, peak_row/peak_nodes (medidos durante la ejecución);
#   * lector exponencial: conjunto de soluciones, comprobadas con CheckerCnf.
# Compara clásico vs bin, y ambos contra la verdad del exhaustivo (veredicto).
#
#   julia --project=.. compare_bin.jl

include("./../src/main.jl")
using Random
include(joinpath(@__DIR__, "generators", "gen_3sat_cnf.jl"))

const ROOT = @__DIR__

# Instancias sembradas adicionales (alrededor de la transición de fase), para llegar a ~80.
const GEN_DIR = joinpath(ROOT, "../test_window/instances_bin")
const FAMILIES = [(4, 12, 15), (5, 20, 15), (6, 26, 15)]

function generate_instances!()
    isdir(GEN_DIR) && return
    mkpath(GEN_DIR)
    Random.seed!(20260925)
    for (n_vars, n_clauses, count) in FAMILIES, i in 1:count
        content = generate_3sat_cnf(n_vars, n_clauses)
        content = join(filter(l -> !startswith(l, "c 2"), split(content, "\n")), "\n")
        write(joinpath(GEN_DIR, "v$(n_vars)_c$(n_clauses)_i$(i).cnf"), content)
    end
end

function corpus()
    dirs = [joinpath(ROOT, "../test/example_cnf"), joinpath(ROOT, "../test_window/instances"), GEN_DIR]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") || continue
            # tseitin (15 vars) es conocido-lento con el mapa bin; se deja fuera del diferencial rápido.
            f == "tseitin_petersen_H.cnf" && continue
            push!(files, joinpath(d, f))
        end
    end
    return files
end

# Verdad (veredicto) por el exhaustivo, reutilizando el caché de salidas si existe.
function truth(path)
    ex = replace(replace(path, "/instances/" => "/solver_exhaustive/"),
                 "/instances_bin/" => "/solver_exhaustive/")
    ex = replace(ex, ".cnf" => ".txt")
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

function row_stats(gpath)
    widths = [line.count for (_, line) in gpath.table_lines.table]
    return (sum(widths), maximum(widths))
end

function run_map(path, loader, first_lit)
    gmap = loader(path)
    machine = SatMachine.new(gmap)
    peak_row = 0
    peak_nodes = 0
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.init!(machine)
        while !SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)
            CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, function (gpath)
                total, widest = row_stats(gpath)
                peak_row = max(peak_row, widest)
                peak_nodes = max(peak_nodes, total)
            end)
            SatMachine.make_step!(machine)
        end
    end
    sat = SatMachine.have_solution(machine)
    sols = Set{BitVector}()
    sols_ok = true
    t_read = 0.0
    if sat
        gpath = first(SatMachine.get_gpath_solutions(machine))
        reader = PathExpReader.new(deepcopy(gpath), first_lit)
        t_read = @elapsed redirect_stdout(devnull) do
            PathExpReader.read!(reader)
        end
        sols = Set(BitVector(s) for s in reader.list_solutions)
        sols_ok = !isempty(sols) && CheckerCnf.test_all(collect(sols), path)
    end
    return (sat = sat, t = t, t_read = t_read, stepcount = gmap.step,
            peak_row = peak_row, peak_nodes = peak_nodes, sols = sols, sols_ok = sols_ok)
end

function main()
    generate_instances!()
    files = corpus()
    n = 0; skipped = 0; notruth = 0
    same_verdict = 0; right = 0; same_sols = 0; bad_check = 0
    t_c = 0.0; t_b = 0.0; tr_c = 0.0; tr_b = 0.0
    max_step_ratio = 0.0; max_node_ratio = 0.0
    for path in files
        tr = truth(path)
        local a, b
        try
            a = run_map(path, GraphMap.load_import!, Step(0))
            b = run_map(path, GraphMapBin.load_import_bin!, Step(1))
        catch e
            skipped += 1
            println("$(basename(path)): SALTADA ($(typeof(e)))")
            continue
        end
        n += 1
        same_verdict += (a.sat == b.sat)
        tr === nothing ? (notruth += 1) : (right += (a.sat == tr && b.sat == tr))
        so = a.sols == b.sols; same_sols += so
        bad_check += !(a.sols_ok && b.sols_ok)
        t_c += a.t; t_b += b.t; tr_c += a.t_read; tr_b += b.t_read
        max_step_ratio = max(max_step_ratio, b.stepcount / a.stepcount)
        max_node_ratio = max(max_node_ratio, b.peak_nodes / max(a.peak_nodes, 1))
        println("$(basename(path)): verdad=$(tr === nothing ? "?" : (tr ? "SAT" : "UNSAT")) " *
                "clásico=$(a.sat) bin=$(b.sat) " *
                "sol=$(so ? "iguales" : "DISTINTAS")($(length(a.sols))/$(length(b.sols))) " *
                "checker=$(a.sols_ok && b.sols_ok ? "ok" : "MAL") " *
                "steps=$(a.stepcount)/$(b.stepcount) peak=$(a.peak_nodes)/$(b.peak_nodes) " *
                "t=$(round(a.t, digits=2))/$(round(b.t, digits=2))s")
    end
    println("── $n instancias ($skipped saltadas, $notruth sin verdad del exhaustivo)")
    println("   mismo veredicto: $same_verdict / $n")
    println("   ambos aciertan la verdad: $right / $(n - notruth)")
    println("   mismas soluciones (lector exponencial): $same_sols / $n")
    println("   instancias con fallo del checker: $bad_check")
    println("   ratio máximo steps (bin/clásico): $(round(max_step_ratio, digits=2))   " *
            "ratio máximo peak_nodes: $(round(max_node_ratio, digits=2))")
    println("   tiempo máquina clásico/bin: $(round(t_c, digits=1)) / $(round(t_b, digits=1)) s   " *
            "lectores: $(round(tr_c, digits=1)) / $(round(tr_b, digits=1)) s")
end

main()
