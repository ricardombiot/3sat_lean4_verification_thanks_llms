# Arnés común de los probes (rama probes-microframework). Junto con src/utils/probes.jl (puntos de sonda sin
# coste y acumuladores) sustituye lo que se repetía en cada probe: corpus, carga del mapa, verdad del exhaustivo
# y volcado a TSV con ERROR por instancia.
#
#   include(joinpath(@__DIR__, "probes_lib.jl"))     # tras include(src/main.jl)
#
#   PROBE_ONLY=a.cnf,b.cnf   solo esas instancias        PROBE_SKIP=x.cnf   se saltan
#   PROBE_LIMIT=N            las N primeras del corpus   PROBE_MAP=bin|classic (para `loader()`)
module ProbeLib
    using Main.AbsSat.Alias: Step
    using Main.AbsSat.GraphMap
    using Main.AbsSat.GraphMapBin
    using Main.AbsSat.ExhaustiveSolver
    using Main.AbsSat.Probes

    const ROOT = abspath(joinpath(@__DIR__, ".."))
    const DIRS = ["test/example_cnf", "test_window/instances", "test_3sat/output/instances",
                  "test_3sat/output_test1/instances", "test_3sat/output_test2/instances",
                  "test_3sat/output_test3/instances", "../../lean/improves_bin/cnf/crafted"]

    # Los dos mapas: (nombre, cargador, primer paso de literales del lector).
    const MAPS = (("classic", GraphMap.load_import!, Step(0)), ("bin", GraphMapBin.load_import_bin!, Step(1)))
    const MAP_BY_NAME = Dict(m[1] => m for m in MAPS)
    map_of_env() = MAP_BY_NAME[get(ENV, "PROBE_MAP", "bin")]

    csv_env(k) = Set(split(get(ENV, k, ""), ","; keepempty = false))

    function corpus(; skip = String[], dirs = DIRS)
        only = csv_env("PROBE_ONLY"); skips = union(csv_env("PROBE_SKIP"), Set(skip))
        files = String[]
        for d in dirs
            dir = joinpath(ROOT, d)
            isdir(dir) || continue
            for f in sort(readdir(dir))
                endswith(f, ".cnf") || continue
                f in skips && continue
                isempty(only) || f in only || continue
                push!(files, joinpath(dir, f))
            end
        end
        lim = parse(Int, get(ENV, "PROBE_LIMIT", "0"))
        return lim > 0 ? files[1:min(end, lim)] : files
    end

    # Las soluciones del exhaustivo (fichero o corriéndolo); nothing si no se puede.
    function exhaustive(path :: String)
        ex = replace(replace(path, "/instances/" => "/solver_exhaustive/"), ".cnf" => ".txt")
        if isfile(ex)
            ls = strip.(readlines(ex))
            return first(ls) == "SAT" ? Set(String.(ls[2:end])) : Set{String}()
        end
        try
            s = ExhaustiveSolver.new(path); ExhaustiveSolver.run!(s)
            return Set(join(Int.(x)) for x in s.list_solutions)
        catch
            return nothing
        end
    end

    """
        run_instances(f, out, header; files = corpus(), variants = (nothing,))

    Escribe el TSV `out`. Para cada instancia (y cada variante, p. ej. cada mapa) llama a `f(path, variant)`, que
    devuelve las columnas de la fila (tras `instance` y, si hay variantes, `variant`). Una excepción da
    «instance ERROR tipo» y sigue.
    """
    function run_instances(f, out :: String, header :: String; files = corpus(), variants = (nothing,))
        open(out, "w") do io
            println(io, header)
            for path in files, v in variants
                head = v === nothing ? basename(path) : "$(basename(path))\t$(v[1])"
                try
                    row = f(path, v)
                    println(io, head, "\t", join(row, "\t"))
                catch e
                    println(io, head, "\tERROR $(typeof(e))")
                end
                flush(io)
            end
        end
    end
end
