# Prototipo: lector por caminos de documentos (30-sept-2026, rama reader-stuck; informe v212 §10, propuesta A).
#
#   PROBE_MAP=bin PROBE_ONLY=a.cnf,b.cnf julia --project=. test_3sat/probe_pathreader.jl <salida.tsv>
#
# Sobre el estado final de la máquina (primer gpath de la solución), tres lectores:
#   col  — el lector actual (PathReader): de abajo arriba, fija el color (nodo del mapa) del primer id de cada paso de
#          literal y revisa.
#   path — A: de arriba abajo. Fija una cima t (un nodo de camino) y después, en cada paso, un padre del último fijado
#          (si hay dos, el primero). SIN RETROCESO: si el estado queda inválido, es un fallo. Tras cada fijación,
#          revisa. Al final hay un nodo por paso.
#   spine — B: de arriba abajo, sin revisión ni retroceso: en cada paso, el primer vivo del estado final vecino de
#           TODO lo elegido.
# Columnas por lector: ok (la asignación leída está en las soluciones del exhaustivo), stuck (se quedó sin candidato
# o la elección dejó el estado inválido), two (pasos con dos candidatos), secs. Y para path/spine: parent (lo elegido fue siempre padre
# del anterior).

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const FIRST_LIT = get(ENV, "PROBE_MAP", "bin") == "bin" ? 1 : 0

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
is_alive(g, x) = PG.is_alive(g.og, x)
is_end(node) = contains(node.title, "or") || contains(node.title, "FusionNode")

# Fija el nodo de camino p en su paso: fuera los demás vivos de ese paso, y revisión.
function pin_node!(g, p)
    for y in alive_at(g, Int(p.id.step))
        y == p && continue
        GraphPath.remove_node_owner!(g, y; rule = :probe)
        g.is_valid || return g
    end
    g.review_owners = true
    g.is_valid && GraphPath.filter!(g, SetNodesId())
    return g
end

# La asignación leída de un nodo por paso (pasos de literal desde FIRST_LIT, de dos en dos, hasta el nodo final).
function bits_of(g, chosen)
    bits = Int[]
    st = FIRST_LIT
    while haskey(chosen, st)
        nd = PathCollectionLines.get_node(g.table_lines, chosen[st])
        (nd === nothing || is_end(nd)) && break
        push!(bits, Int(chosen[st].id.index))
        st += 2
    end
    return join(bits)
end

function read_path(g0)
    # SIN RETROCESO: la primera cima, y en cada paso el primer padre; si el estado queda inválido, fallo.
    top = Int(g0.current_step) - 1
    two = 0; parent = true
    t = sort(alive_at(g0, top), by = string)[1]
    g = pin_node!(deepcopy(g0), t)
    g.is_valid || return (nothing, Dict{Int, PathNodeId}(), 1, two, parent)
    chosen = Dict(top => t)
    x = t
    for s in (top - 1):-1:0
        nd = PathCollectionLines.get_node(g.table_lines, x)
        cands = nd === nothing ? PathNodeId[] :
                [p for p in nd.parents if is_alive(g, p) && PG.has_edge(g.og, x, p)]
        if isempty(cands)
            cands = alive_at(g, s)
            parent = false
        end
        isempty(cands) && return (nothing, chosen, 1, two, parent)
        length(cands) >= 2 && (two += 1)
        p = sort(cands, by = string)[1]
        g = pin_node!(g, p)
        (g.is_valid && is_alive(g, x)) || return (nothing, chosen, 1, two, parent)
        chosen[s] = p; x = p
    end
    return (g, chosen, 0, two, parent)
end

function read_spine(g0)
    # SIN RETROCESO: la primera cima y el primer candidato de cada paso.
    top = Int(g0.current_step) - 1
    adj(a, b) = a == b || PG.has_edge(g0.og, a, b)
    two = 0; parent = true
    t = sort(alive_at(g0, top), by = string)[1]
    chosen = Dict(top => t)
    for s in (top - 1):-1:0
        cands = [r for r in alive_at(g0, s) if all(x -> adj(x, r), values(chosen))]
        isempty(cands) && return (Dict{Int, PathNodeId}(), 1, two, parent)
        length(cands) >= 2 && (two += 1)
        r = sort(cands, by = string)[1]
        nd = PathCollectionLines.get_node(g0.table_lines, chosen[s + 1])
        (nd === nothing || !(r in nd.parents)) && (parent = false)
        chosen[s] = r
    end
    return (chosen, 0, two, parent)
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = ("sat", "col_ok", "col_secs", "path_ok", "path_stuck", "path_two", "path_parent", "path_secs",
            "spine_ok", "spine_stuck", "spine_two", "spine_parent", "spine_secs", "machine_secs")
    header = "instance\ttruth\t" * join(cols, "\t")
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        machine = SatMachine.new(loader(path))
        tm = @elapsed redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
        sat = SatMachine.have_solution(machine)
        sat || return (truth, false, "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", round(tm, digits = 2))
        g0 = first(SatMachine.get_gpath_solutions(machine))
        check(b) = ex === nothing ? "?" : string(b in ex)
        # lector por colores
        local cbits
        tc = @elapsed begin
            r = PathReader.new(deepcopy(g0), Step(FIRST_LIT))
            PathReader.read!(r)
            cbits = join(Int.(r.solution))
        end
        # lector por caminos
        local pres
        tp = @elapsed pres = read_path(g0)
        (gp, chp, pst, ptw, ppa) = pres
        pbits = gp === nothing ? "" : bits_of(gp, chp)
        # espina
        local sres
        ts = @elapsed sres = read_spine(g0)
        (chs, sst, stw, spa) = sres
        sbits = isempty(chs) ? "" : bits_of(g0, chs)
        return (truth, true, check(cbits), round(tc, digits = 3),
                gp === nothing ? "false" : check(pbits), pst, ptw, ppa, round(tp, digits = 3),
                isempty(chs) ? "false" : check(sbits), sst, stw, spa, round(ts, digits = 3), round(tm, digits = 2))
    end
end

main()
