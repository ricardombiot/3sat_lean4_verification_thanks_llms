# Cuánto ve un trío, y cuánto falta para la mayoría (2-oct-2026, rama reader-stuck; tras el v221).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_regen.jl <salida.tsv>
#
# Con FORBID = :on, sobre las uniones revisadas (jrev) y los estados finales revisados (fin). Se enumeran las camarillas
# de cada estado (tope REGEN_CAP) y se miden dos cosas:
#
# (1) Determinación: en cuántas camarillas está cada nodo, arista y triángulo que está en alguna.
#       n / n1, e / e1, t / t1     total y los que están en UNA sola camarilla (el objeto ya fija la solución entera)
#       t_max                      el mayor número de camarillas por un triángulo
#     Si casi todo triángulo está en una sola camarilla, el nivel 3 ve la solución completa: la exactitud del nivel 3
#     dice poco sobre instancias con más variables.
#
# (2) Mayoría por parejas (el paso de la prueba 2-CNF): para tres aristas vivas entre los mismos dos pasos, la pareja
#     «mayoría» (bit a bit sobre la ventana id / padre / abuelo de cada extremo).
#       m_tri      tríos de aristas probados (hasta REGEN_SAMPLE por par de pasos) cuya mayoría no es una de las tres
#       m_ok       la pareja mayoría es una arista viva
#       m_node     alguna de las dos ventanas mayoría no está viva (p. ej. la ventana prohibida de una cláusula)
#       m_edge     las dos ventanas viven y no son vecinas: el fallo propio de 3-CNF a nivel de parejas
# Con varios estados, las sumas (t_max: el máximo).

using Random
const OUT = abspath(ARGS[1])
const CAP = parse(Int, get(ENV, "REGEN_CAP", "50000"))
const SAMPLE = parse(Int, get(ENV, "REGEN_SAMPLE", "200"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = MersenneTwister(1)

function reviewed(g)
    h = deepcopy(g)
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

maj(a, b, c) = a == b ? a : (a == c ? a : b)          # con dos valores posibles, el repetido
majid(a :: Nothing, b, c) = nothing
majid(a :: NodeId, b :: NodeId, c :: NodeId) = (step = a.step, index = maj(a.index, b.index, c.index))
majnode(x, y, z) = PathNodeId(majid(x.gparent_id, y.gparent_id, z.gparent_id),
                              majid(x.parent_id, y.parent_id, z.parent_id), majid(x.id, y.id, z.id))

function judge(g, pre)
    g.is_valid || return
    og = g.og
    top = Int(g.current_step) - 1
    top >= 2 || return
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    # camarillas y multiplicidades
    N = Dict{PathNodeId, Int}(); E = Dict{NTuple{2, PathNodeId}, Int}(); T = Dict{NTuple{3, PathNodeId}, Int}()
    cliq = Ref(0); chain = PathNodeId[]
    ok(p) = all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        cliq[] > CAP && return
        push!(chain, x)
        if s == 0
            cliq[] += 1
            L = length(chain)
            for i in 1:L
                N[chain[i]] = get(N, chain[i], 0) + 1
                for j in (i + 1):L
                    k2 = (chain[j], chain[i]); E[k2] = get(E, k2, 0) + 1
                    for k in (j + 1):L
                        k3 = (chain[k], chain[j], chain[i]); T[k3] = get(T, k3, 0) + 1
                    end
                end
            end
        else
            foreach(p -> dfs(p, s - 1), [p for p in alive[s - 1] if ok(p)])
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, top), alive[top])
    cliq[] > CAP && (bump(Symbol(pre, "_cap")); return)
    bump(Symbol(pre, "_states")); bump(Symbol(pre, "_cliq"), cliq[])
    for (D, nm) in ((N, "n"), (E, "e"), (T, "t"))
        bump(Symbol(pre, "_", nm), length(D)); bump(Symbol(pre, "_", nm, "1"), count(==(1), values(D)))
    end
    isempty(T) || (C[Symbol(pre, "_t_max")] = max(get(C, Symbol(pre, "_t_max"), 0), maximum(values(T))))
    # mayoría por parejas
    for l in 0:top, j in (l + 1):top
        es = [(a, b) for a in alive[l] for b in PG.neighbors(og, a, Step(j)) if PG.is_alive(og, b)]
        length(es) >= 3 || continue
        seen = Set{NTuple{3, Int}}()
        tries = min(SAMPLE, binomial(length(es), 3))
        for _ in 1:(4 * tries)
            length(seen) >= tries && break
            ix = Tuple(sort(randperm(RNG, length(es))[1:3]))
            ix in seen && continue
            push!(seen, ix)
            (a1, b1), (a2, b2), (a3, b3) = es[ix[1]], es[ix[2]], es[ix[3]]
            ma = majnode(a1, a2, a3); mb = majnode(b1, b2, b3)
            ((ma, mb) == (a1, b1) || (ma, mb) == (a2, b2) || (ma, mb) == (a3, b3)) && continue
            bump(Symbol(pre, "_m_tri"))
            if !(PG.is_alive(og, ma) && PG.is_alive(og, mb))
                bump(Symbol(pre, "_m_node"))
            elseif PG.has_edge(og, ma, mb)
                bump(Symbol(pre, "_m_ok"))
            else
                bump(Symbol(pre, "_m_edge"))
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    groups = ("jrev", "fin")
    fields = ("states", "cap", "cliq", "n", "n1", "e", "e1", "t", "t1", "t_max", "m_tri", "m_ok", "m_node", "m_edge")
    cols = [Symbol(g, "_", f) for g in groups for f in fields]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            Probes.with(:join_post => g -> judge(reviewed(g), "jrev")) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
            if SatMachine.have_solution(machine)
                for g in SatMachine.get_gpath_solutions(machine)
                    judge(reviewed(g), "fin")
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
