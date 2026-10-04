# Regla de tríos (29-sept-2026, rama reader-stuck; GraphPath.TRIO_RULE en graph_path_filter_pair.jl).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_trio.jl <salida.tsv>
#
# Para cada instancia, la máquina y el lector (PathExpReader, todas las ramas) con TRIO_RULE = :off, :clause y :on:
#   truth                 — verdad del exhaustivo
#   v_off, v_cl, v_on     — veredictos de la máquina
#   ok_cl, ok_on          — con la regla, las soluciones del lector son exactamente las del exhaustivo
#   same_cl, same_on      — misma línea final que con :off (vivos, aristas, nodos y enlaces)
#   cut_cl, cut_on        — aristas que corta la regla de tríos y no la de parejas
#   e_off, e_cl, e_on     — aristas en la línea final
#   t_off, t_cl, t_on     — tiempo de máquina + lector

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step
using .AbsSat.Probes

key(id) = Alias.as_key(id)

function fingerprint(machine)
    out = String[]
    for g in SatMachine.get_gpath_list(machine)
        nodes = String[]
        PathCollectionLines.for_each(g.table_lines, n -> push!(nodes,
            key(n.id) * "|p:" * join(sort(key.(collect(n.parents))), ",") * "|s:" * join(sort(key.(collect(n.sons))), ",")))
        push!(out, string(key(g.map_parent_id), " valid=", g.is_valid,
            " alive=", join(sort(key.(collect(GraphPath.alive_ids(g)))), ","),
            " edges=", join(sort([key(a) * "-" * key(b) for (a, b) in keys(g.og.edges)]), ","),
            " nodes=", join(sort(nodes), ";")))
    end
    return join(sort(out), "\n")
end

nedges(machine) = sum(length(g.og.edges) for g in SatMachine.get_gpath_list(machine); init = 0)

function run(path, loader, first_lit, mode)
    GraphPath.TRIO_RULE[] = mode
    GraphPath.TRIO_REMOVED[] = 0
    machine = SatMachine.new(loader(path))
    sols = Set{String}()
    t = @elapsed begin
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
        if SatMachine.have_solution(machine)
            reader = PathExpReader.new(deepcopy(first(SatMachine.get_gpath_solutions(machine))), first_lit)
            redirect_stdout(devnull) do
                PathExpReader.read!(reader)
            end
            sols = Set(join(Int.(s)) for s in reader.list_solutions)
        end
    end
    return (sat = SatMachine.have_solution(machine), sols = sols, fp = fingerprint(machine), t = t,
            cut = GraphPath.TRIO_REMOVED[], e = nedges(machine))
end

function main()
    _, loader, fl = ProbeLib.map_of_env()
    header = "instance\ttruth\tv_off\tv_cl\tv_on\tok_off\tok_cl\tok_on\tsame_cl\tsame_on\tcut_cl\tcut_on\t" *
             "e_off\te_cl\te_on\tt_off\tt_cl\tt_on"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        a = run(path, loader, fl, :off)
        c = run(path, loader, fl, :clause)
        o = run(path, loader, fl, :on)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        ok(r) = ex === nothing ? "?" : string(r.sols == ex)
        return (truth, a.sat, c.sat, o.sat, ok(a), ok(c), ok(o), a.fp == c.fp, a.fp == o.fp, c.cut, o.cut,
                a.e, c.e, o.e, round(a.t, digits = 2), round(c.t, digits = 2), round(o.t, digits = 2))
    end
    GraphPath.TRIO_RULE[] = :off
end

main()
