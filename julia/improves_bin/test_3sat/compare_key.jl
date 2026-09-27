# Diferencial de las reglas de la fila de claves (informe v196 §3 y §3.5), mapa bin.
#
# Cuatro modos: sin reglas (off/off), solo etiqueta (KEY_MODE), solo comprobación (KEYCHECK_MODE) y las dos.
# Por instancia y modo:
#   * la máquina: veredicto (contra el exhaustivo si hay), pico de nodos de un estado, vueltas del review, tiempo;
#   * el lector sin retroceso (PathReader): si su asignación pasa el checker;
#   * el lector exponencial: el conjunto de soluciones leídas;
#   * contadores de las reglas en la máquina: joins con etiqueta, fijaciones de clave, entradas cortadas por la
#     etiqueta, copias y claves quitadas por la comprobación.
#
#   julia --project=.. compare_key.jl [f1.cnf ...]     (sin argumentos: el corpus de abajo)

include("./../src/main.jl")

const ROOT = @__DIR__
const MODES = [(:off, :off), (:on, :off), (:off, :on), (:on, :on)]
modename(m) = m == (:off, :off) ? "ninguna" : m == (:on, :off) ? "etiqueta" : m == (:off, :on) ? "comprobación" : "las dos"

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

function run_mode(path, mode)
    GraphPath.KEY_MODE[] = mode[1]
    GraphPath.KEYCHECK_MODE[] = mode[2]
    GraphPath.REVIEW_ROUNDS[] = 0
    GraphPath.reset_key_counters!()
    gmap = GraphMapBin.load_import_bin!(path)
    machine = SatMachine.new(gmap)
    peak = 0
    t = @elapsed redirect_stdout(devnull) do
        SatMachine.init!(machine)
        while !SatMachine.is_finished(machine) && SatMachine.have_gpaths_step(machine)
            CollectionTimeline.for_each_gpath(machine.timeline, machine.current_step, function (g)
                peak = max(peak, sum(line.count for (_, line) in g.table_lines.table; init = 0))
            end)
            SatMachine.make_step!(machine)
        end
    end
    cm = (joins = GraphPath.KEY_JOINS[], restricts = GraphPath.KEY_RESTRICTS[], cut = GraphPath.KEY_CUT[],
          copies = GraphPath.KEYCHECK_COPIES[], removed = GraphPath.KEYCHECK_REMOVED[])
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
    (sat = sat, t = t, t_read = t_read, peak = peak, rounds = rounds, plain_ok = plain_ok, sols = sols, cm = cm)
end

function main()
    files = isempty(ARGS) ? corpus() : ARGS
    agg = Dict(m => Dict(:right => 0, :wrong => 0, :plainbad => 0, :t => 0.0, :rounds => 0, :peak => 0,
                         :joins => 0, :restricts => 0, :cut => 0, :copies => 0, :removed => 0) for m in MODES)
    n = 0; diffsols = 0
    for path in files
        tr = truth(path)
        res = Dict{Any, Any}()
        try
            for m in MODES; res[m] = run_mode(path, m); end
        catch e
            println("$(basename(path)): SALTADA ($(typeof(e)): $e)"); continue
        end
        n += 1
        base = res[(:off, :off)]
        any(m -> res[m].sols != base.sols, MODES) && (diffsols += 1)
        line = "$(basename(path)): verdad=$(tr === nothing ? "?" : (tr ? "SAT" : "UNSAT"))"
        for m in MODES
            r = res[m]; a = agg[m]
            tr === nothing || (r.sat == tr ? (a[:right] += 1) : (a[:wrong] += 1))
            r.sat && !r.plain_ok && (a[:plainbad] += 1)
            a[:t] += r.t + r.t_read; a[:rounds] += r.rounds; a[:peak] = max(a[:peak], r.peak)
            for k in (:joins, :restricts, :cut, :copies, :removed); a[k] += getfield(r.cm, k); end
            line *= " | $(modename(m)): $(r.sat ? "SAT" : "UNSAT")$(r.sat && !r.plain_ok ? " (lector MAL)" : "") " *
                    "pico $(r.peak) vueltas $(r.rounds) corta $(r.cm.cut) quita $(r.cm.removed) $(round(r.t + r.t_read, digits = 2))s"
        end
        println(line); flush(stdout)
    end
    println("── $n instancias; con soluciones del lector exponencial distintas entre modos: $diffsols")
    for m in MODES
        a = agg[m]
        println("   $(modename(m)): aciertos $(a[:right]), fallos $(a[:wrong]), lector sin retroceso MAL $(a[:plainbad]), " *
                "tiempo $(round(a[:t], digits = 1)) s, vueltas $(a[:rounds]), pico $(a[:peak]); " *
                "joins etiquetados $(a[:joins]), fijaciones de clave $(a[:restricts]), entradas cortadas $(a[:cut]), " *
                "copias $(a[:copies]), claves quitadas $(a[:removed])")
    end
end

main()
