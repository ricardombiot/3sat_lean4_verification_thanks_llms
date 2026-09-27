# Diferencial de las etiquetas de clave de todos los niveles (informe v197 §5), mapa bin: KEYTAGS_MODE :off frente a :on.
#
# Por instancia y modo:
#   * la máquina: veredicto (contra el exhaustivo si lo hay), pico de nodos de un estado, vueltas del review, tiempo;
#   * el lector sin retroceso (PathReader): si su asignación pasa el checker;
#   * el lector exponencial: el conjunto de soluciones leídas (debe ser el mismo en los dos modos);
#   * con :on, la mezcla: filas de claves mezcladas y máscaras guardadas frente a entradas de las tablas (pico en la
#     máquina), y los contadores de la regla.
#
#   julia --project=.. compare_keytags.jl [f1.cnf ...]     (sin argumentos: el corpus de abajo)

include("./../src/main.jl")

const ROOT = @__DIR__

function corpus()
    dirs = [joinpath(ROOT, "../test/example_cnf"), joinpath(ROOT, "../test_window/instances"),
            joinpath(ROOT, "../../../lean/improves_bin/cnf/crafted"), joinpath(ROOT, "../../../lean/improves_bin/cnf/random_small")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") || continue
            f == "tseitin_petersen_H.cnf" && continue    # conocido-lento con el mapa bin
            push!(files, joinpath(d, f))
        end
    end
    files
end

function truth(path)
    try
        solver = ExhaustiveSolver.new(path)
        redirect_stdout(devnull) do; ExhaustiveSolver.run!(solver); end
        return !isempty(solver.list_solutions)
    catch
        return nothing
    end
end

n_entries(g) = sum(length(set) for (_, line) in g.table_lines.table for (_, node) in line.table for (_, set) in node.owners.table; init = 0)
n_nodes(g) = sum(line.count for (_, line) in g.table_lines.table; init = 0)

# Mezcla de un estado: (filas mezcladas, filas con etiqueta, máscaras guardadas, entradas).
function mixing(g)
    t = g.key_tags
    t === nothing && return (0, 0, 0, n_entries(g))
    (length(t.mixed), length(t.mixed) + length(t.uniform), sum(length(m) for (_, m) in t.mixed; init = 0), n_entries(g))
end

function run_mode(path, mode)
    GraphPath.KEYTAGS_MODE[] = mode
    GraphPath.REVIEW_ROUNDS[] = 0
    GraphPath.reset_keytags_counters!()
    machine = SatMachine.new(GraphMapBin.load_import_bin!(path))
    peak = 0; mix_rows = 0; mix_rows_of = 0; ratio = 0.0
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.init!(machine)
        while !SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)
            CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, function (g)
                peak = max(peak, n_nodes(g))
                mr, rows, masks, es = mixing(g)
                if mr > mix_rows; mix_rows = mr; mix_rows_of = rows; end
                es > 0 && (ratio = max(ratio, masks / es))
            end)
            SatMachine.make_step!(machine)
        end
    end
    cm = (cut = GraphPath.KEYTAGS_CUT[], restricts = GraphPath.KEYTAGS_RESTRICTS[], material = GraphPath.KEYTAGS_MATERIAL[],
          missing = GraphPath.KEYTAGS_MISSING[], dropped = GraphPath.KEYTAGS_DROPPED[])
    rounds = GraphPath.REVIEW_ROUNDS[]
    sat = SatMachine.have_solution(machine)
    plain_ok = true; sols = Set{BitVector}(); t_read = 0.0
    if sat
        gpath = first(SatMachine.get_gpath_solutions(machine))
        t_read = @elapsed begin
            reader = PathReader.new(deepcopy(gpath), Step(1))
            try
                redirect_stdout(devnull) do; PathReader.read!(reader); end
                plain_ok = CheckerCnf.test_all([reader.solution], path)
            catch
                plain_ok = false
            end
            exp = PathExpReader.new(deepcopy(gpath), Step(1))
            redirect_stdout(devnull) do; PathExpReader.read!(exp); end
            sols = Set(BitVector(s) for s in exp.list_solutions)
        end
    end
    (sat = sat, t = t, t_read = t_read, peak = peak, rounds = rounds, plain_ok = plain_ok, sols = sols, cm = cm,
     mix_rows = mix_rows, mix_rows_of = mix_rows_of, ratio = ratio)
end

function main()
    files = isempty(ARGS) ? corpus() : ARGS
    n = 0; diffsols = 0; right = Dict(:off => 0, :on => 0); wrong = Dict(:off => 0, :on => 0)
    plainbad = Dict(:off => 0, :on => 0); tt = Dict(:off => 0.0, :on => 0.0); rr = Dict(:off => 0, :on => 0)
    peakdiff = 0; tot = Dict(:cut => 0, :restricts => 0, :material => 0, :missing => 0, :dropped => 0)
    maxratio = 0.0; fullmix = 0
    for path in files
        tr = truth(path)
        local a, b
        try
            a = run_mode(path, :off); b = run_mode(path, :on)
        catch e
            println("$(basename(path)): SALTADA ($(typeof(e)): $e)"); continue
        end
        n += 1
        a.sols != b.sols && (diffsols += 1)
        for (m, r) in ((:off, a), (:on, b))
            tr === nothing || (r.sat == tr ? (right[m] += 1) : (wrong[m] += 1))
            r.sat && !r.plain_ok && (plainbad[m] += 1)
            tt[m] += r.t + r.t_read; rr[m] += r.rounds
        end
        a.peak != b.peak && (peakdiff += 1)
        for k in keys(tot); tot[k] += getfield(b.cm, k); end
        maxratio = max(maxratio, b.ratio)
        b.mix_rows_of > 0 && b.mix_rows >= b.mix_rows_of - 2 && (fullmix += 1)
        println("$(basename(path)): verdad=$(tr === nothing ? "?" : (tr ? "SAT" : "UNSAT")) off=$(a.sat ? "SAT" : "UNSAT") on=$(b.sat ? "SAT" : "UNSAT")" *
                "$(a.sols == b.sols ? "" : " SOLUCIONES DISTINTAS")$(b.sat && !b.plain_ok ? " (lector MAL)" : "") " *
                "pico $(a.peak)/$(b.peak) vueltas $(a.rounds)/$(b.rounds) corta $(b.cm.cut) " *
                "filas mezcladas $(b.mix_rows)/$(b.mix_rows_of) máscaras/entradas $(round(b.ratio, digits = 1)) " *
                "tiempo $(round(a.t + a.t_read, digits = 2))/$(round(b.t + b.t_read, digits = 2))s")
        flush(stdout)
    end
    println("── $n instancias; soluciones del lector exponencial distintas entre modos: $diffsols; pico de nodos distinto: $peakdiff")
    for m in (:off, :on)
        println("   $m: aciertos $(right[m]), fallos $(wrong[m]), lector sin retroceso MAL $(plainbad[m]), tiempo $(round(tt[m], digits = 1)) s, vueltas $(rr[m])")
    end
    println("   on: entradas cortadas $(tot[:cut]), fijaciones sobre filas mezcladas $(tot[:restricts]), filas materializadas $(tot[:material]), " *
            "entradas sin máscara $(tot[:missing]), filas descartadas $(tot[:dropped])")
    println("   mezcla: instancias con (casi) todas las filas mezcladas $fullmix; máximo de máscaras/entradas en un estado $(round(maxratio, digits = 1))")
end

main()
