# Comparison harness for the PathNodeId window refactor.
#
#   julia compare.jl W=2 out=baseline_w2.tsv
#   julia compare.jl W=3 out=w3.tsv
#
# Runs SatMachine and the exhaustive solver on the seeded instances in ./instances
# (generated on first use) and writes one TSV row per instance.
include("./../src/main.jl")
using Random
include(joinpath(@__DIR__, "..", "test_3sat", "generators", "gen_3sat_cnf.jl"))

const INSTANCES_DIR = joinpath(@__DIR__, "instances")
# (variables, clauses, count) around the 3-SAT phase transition, so SAT and UNSAT both appear.
const FAMILIES = [(4, 12, 6), (5, 20, 6), (6, 26, 6), (7, 30, 4)]

function generate_instances!()
    isdir(INSTANCES_DIR) && return
    mkpath(INSTANCES_DIR)
    Random.seed!(20260920)
    for (n_vars, n_clauses, count) in FAMILIES, i in 1:count
        content = generate_3sat_cnf(n_vars, n_clauses)
        content = join(filter(l -> !startswith(l, "c 2"), split(content, "\n")), "\n")
        write(joinpath(INSTANCES_DIR, "v$(n_vars)_c$(n_clauses)_i$(i).cnf"), content)
    end
end

function row_stats(gpath :: GPath) :: Tuple{Int, Int}
    widths = [line.count for (_, line) in gpath.table_lines.table]
    return (sum(widths), maximum(widths))
end

function run_instance(path :: String)
    ex = ExhaustiveSolver.new(path)
    ExhaustiveSolver.run!(ex)
    ex_sat = !isempty(ex.list_solutions)

    total_nodes, max_row, m_nsol, valid = 0, 0, 0, true
    elapsed = @elapsed begin
        gmap = GraphMap.load_import!(path)
        machine = SatMachine.new(gmap)
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
    end
    m_sat = SatMachine.have_solution(machine)
    if m_sat
        gpath = first(SatMachine.get_gpath_solutions(machine))
        total_nodes, max_row = row_stats(gpath)
        reader = PathExpReader.new(gpath)
        redirect_stdout(devnull) do
            PathExpReader.read!(reader)
        end
        m_nsol = length(reader.list_solutions)
        valid = CheckerCnf.test_all(reader.list_solutions, path)
    end
    return (ex_sat, m_sat, length(ex.list_solutions), m_nsol, valid, total_nodes, max_row, elapsed)
end

function main(args)
    params = Dict(split(a, "=")[1] => split(a, "=")[2] for a in args)
    window = parse(Int, get(params, "W", "3"))
    out = get(params, "out", "result_w$(window).tsv")
    if isdefined(Main.AbsSat.Alias, :WINDOW)
        Main.AbsSat.Alias.WINDOW[] = window
    elseif window != 2
        error("this checkout has no Alias.WINDOW, only W=2 is possible")
    end

    generate_instances!()
    open(out, "w") do io
        println(io, "instance\tex_sat\tm_sat\tex_nsol\tm_nsol\tm_valid\ttotal_nodes\tmax_row\tsecs")
        for file in sort(readdir(INSTANCES_DIR))
            endswith(file, ".cnf") || continue
            row = try
                run_instance(joinpath(INSTANCES_DIR, file))
            catch e
                ("ERR", first(split(sprint(showerror, e), "\n")), 0, 0, false, 0, 0, 0.0)
            end
            secs = row[end] isa Float64 ? round(row[end], digits=2) : row[end]
            println(io, join([file; collect(row[1:end-1]); secs], "\t"))
            flush(io)
            println("$file  ex=$(row[1]) machine=$(row[2]) valid=$(row[5]) nodes=$(row[6]) secs=$secs")
        end
    end
end

main(ARGS)
