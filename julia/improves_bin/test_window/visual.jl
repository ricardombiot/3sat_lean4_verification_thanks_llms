# Draws the final gpath of one instance.
#   julia visual.jl W=3 cnf=tiny.cnf out=/some/dir
include("./../src/main.jl")

function main(args)
    params = Dict(split(a, "=")[1] => split(a, "=")[2] for a in args)
    window = parse(Int, get(params, "W", "3"))
    cnf = get(params, "cnf", joinpath(@__DIR__, "tiny.cnf"))
    out = String(get(params, "out", "."))
    Main.AbsSat.Alias.WINDOW[] = window
    mkpath(out)

    machine = SatMachine.new(GraphMap.load_import!(cnf))
    redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    SatMachine.have_solution(machine) || error("UNSAT instance: no final gpath to draw")
    gpath = first(SatMachine.get_gpath_solutions(machine))

    widths = sort([(step, line.count) for (step, line) in gpath.table_lines.table])
    println("W=$window rows=$(length(widths)) nodes=$(sum(last.(widths))) widths=$(last.(widths))")
    GraphPathVisual.to_png(GraphPathVisual.build(gpath), "gpath_w$(window)", out)
end

main(ARGS)
