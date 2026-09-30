# El cuarteto vivo y la extensión de camarillas vivas (30-sept-2026, rama reader-stuck; tras probe_forbid).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_quartet.jl <salida.tsv> [lecturas]
#
# Sobre el primer estado final con FORBID = :on (y, para comparar, con :off, donde no hay tríos prohibidos):
#   una camarilla es VIVA si sus nodos son vecinos dos a dos y ninguno de sus tríos está prohibido.
#   q_trios, q_fail  — tríos vivos y cuántos NO tienen, en algún paso, un nodo que forme con ellos un cuarteto vivo
#                      (con :on es 0 por construcción: es el punto fijo de forbid_rule!)
#   td_*             — camarillas crecidas de la cima abajo (la espina), eligiendo al azar entre los que la extienden
#                      viva: runs, stuck (algún paso sin extensión), k_min (tamaño de la camarilla más pequeña atascada)
#   rnd_*            — lo mismo con los pasos en orden aleatorio
#   *_bad            — camarillas completas que no son solución (con :on deben ser 0: tríos sólidos no bastan, pero una
#                      camarilla completa del estado final sí es solución, Decode)
#   Mismas columnas con prefijo off_ para el estado con FORBID = :off (camarilla viva = vecinos dos a dos).

using Random
const OUT = abspath(ARGS[1])
const RUNS = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 200
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(20260930))
const FIRST_LIT = get(ENV, "PROBE_MAP", "bin") == "bin" ? 1 : 0

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b || PG.has_edge(g.og, a, b)
dead(g, a, b, r) = length(unique((a, b, r))) == 3 && PG.dead_trio(g.og, a, b, r)

# r extiende la camarilla viva C (vecino de todos, sin trío prohibido con ninguna pareja de C)
extends(g, C, r) = all(x -> adj(g, x, r), C) &&
    !any(dead(g, C[i], C[j], r) for i in eachindex(C) for j in i+1:length(C))

function bits_of(g, chosen)
    bits = Int[]; st = FIRST_LIT
    while haskey(chosen, st)
        nd = PathCollectionLines.get_node(g.table_lines, chosen[st])
        (nd === nothing || contains(nd.title, "or") || contains(nd.title, "FusionNode")) && break
        push!(bits, Int(chosen[st].id.index)); st += 2
    end
    return join(bits)
end

# Tríos vivos sin cuarteto vivo en algún paso.
function quartet(g)
    T = Int(g.current_step)
    n = 0; fail = 0
    for e in values(g.og.edges), r in collect(PG.neighbors_all(g.og, e.a))
        (r == e.a || r == e.b || !(PG.node_ord(e.b) < PG.node_ord(r))) && continue
        adj(g, e.b, r) || continue
        dead(g, e.a, e.b, r) && continue
        n += 1
        C = [e.a, e.b, r]
        steps = Set(Int(x.id.step) for x in C)
        all(l -> l in steps || any(s -> extends(g, C, s), alive_at(g, l)), 0:T-1) || (fail += 1)
    end
    return n, fail
end

# Crece una camarilla viva por los pasos en `order`; devuelve (atascada?, tamaño al atascarse, elegidos).
function grow(g, order, rng)
    C = PathNodeId[]; chosen = Dict{Int, PathNodeId}()
    for s in order
        cands = [r for r in alive_at(g, s) if extends(g, C, r)]
        isempty(cands) && return (true, length(C), chosen)
        r = rand(rng, cands); push!(C, r); chosen[s] = r
    end
    return (false, length(C), chosen)
end

function judge(g, ex)
    T = Int(g.current_step)
    qn, qf = quartet(g)
    res = Any[qn, qf]
    for mode in (:td, :rnd)
        stuck = 0; kmin = typemax(Int); bad = 0
        for _ in 1:RUNS
            order = mode == :td ? collect(T-1:-1:0) : shuffle(RNG[], collect(0:T-1))
            st, k, ch = grow(g, order, RNG[])
            if st
                stuck += 1; kmin = min(kmin, k)
            elseif ex !== nothing && !(bits_of(g, ch) in ex)
                bad += 1
            end
        end
        push!(res, RUNS, stuck, kmin == typemax(Int) ? "-" : kmin, bad)
    end
    return res
end

function final_state(path, loader, mode)
    PG.FORBID[] = mode
    machine = SatMachine.new(loader(path))
    redirect_stdout(devnull) do
        SatMachine.run!(machine)
    end
    PG.FORBID[] = :off
    SatMachine.have_solution(machine) || return nothing
    return first(SatMachine.get_gpath_solutions(machine))
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = ["q_trios", "q_fail", "td_runs", "td_stuck", "td_kmin", "td_bad", "rnd_runs", "rnd_stuck", "rnd_kmin", "rnd_bad"]
    header = "instance\ttruth\t" * join(cols, "\t") * "\t" * join("off_" .* cols, "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        t = @elapsed begin
            g1 = final_state(path, loader, :on)
            g0 = final_state(path, loader, :off)
            r1 = g1 === nothing ? fill("-", length(cols)) : judge(g1, ex)
            r0 = g0 === nothing ? fill("-", length(cols)) : judge(g0, ex)
        end
        return (truth, r1..., r0..., round(t, digits = 1))
    end
end

main()
