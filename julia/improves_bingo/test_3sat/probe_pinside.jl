# PinSideOn: (★) con pins y tríos reales (1-oct-2026, rama reader-stuck; lean ForbidOnGood.lean, PinSideOn).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_pinside.jl <salida.tsv> [muestras]
#
#   PIN_MODE=random (por defecto) | real
#
# Con FORBID = :on (el modo del enunciado Lean). En cada join (:join_pre / :join_post), para R = [] y para pins R:
#   random — al azar, 1-3 nodos de mapa por debajo de la cima (PinSideOn, todo pin);
#   real   — los que la máquina usa (Lean PinsFrom): los requisitos de un camino del mapa al azar desde el destino del
#            join, cortado a una longitud al azar o hasta el final (la hipótesis de spineVerdictOn_iff_of_joinOn).
# U = pin(join(A,B), R), PA = pin(A, R), PB = pin(B, R), con
# pin = filtro + revisión con la regla (Lean pinOn). Se recorren todas las cadenas vivas de U (de una cima hacia abajo
# por padres del documento, vecinos dos a dos, sin trío prohibido en U) y, para cada una, si es cadena viva de PA o de
# PB (lado válido, nodos vivos, parejas vecinas, enlaces padre en el documento del lado, sin trío prohibido allí).
#   runs       — uniones fijadas válidas
#   chains     — cadenas vivas de U (cada prefijo cuenta)
#   none       — cadenas que no son vivas en ningún lado (PinSideOn pide 0)
#   both       — cadenas vivas en los dos lados
#   n_node, n_edge, n_link, n_trio — por qué falla el lado de la cima en las cadenas `none` (primer motivo)
#   n_invalid  — el lado de la cima no es válido
#   dead       — callejones de U (control: LiveExt de la unión fijada)
#   side_dead  — callejones de PA y PB (control: GoodOn de los lados)
#   cap        — uniones fijadas donde se cortó el recorrido

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 3
const CAP = 20000
const RAM_MB = parse(Int, get(ENV, "PROBE_RAM_MB", "3500"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20261001))
const PIN_MODE = get(ENV, "PIN_MODE", "random")
const GMAP = Ref{Any}(nothing)
const PRE = Ref{Any}(nothing)

ram_ok() = Sys.maxrss() / 2^20 < RAM_MB
alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b ? PG.is_alive(g.og, a) : PG.has_edge(g.og, a, b)
dead(g, a, b, r) = length(unique((a, b, r))) == 3 && PG.has_edge(g.og, a, b) && PG.dead_trio(g.og, a, b, r)

function random_pins(g, n)
    top = Int(g.current_step) - 1
    steps = [s for s in 1:top-1 if length(unique(x.id for x in alive_at(g, s))) >= 2]
    isempty(steps) && return NodeId[]
    [begin ids = unique(x.id for x in alive_at(g, s)); ids[rand(RNG[], 1:length(ids))] end
     for s in shuffle(RNG[], steps)[1:min(n, length(steps))]]
end
# Los requisitos de un camino del mapa al azar desde `d`, cortado a una longitud al azar (o hasta el final).
function real_pins(d)
    R = NodeId[]
    last = Int(GMAP[].step) - 1
    len = rand(RNG[], Bool) ? typemax(Int) : rand(RNG[], 1:max(1, last - Int(d.step)))
    k = d
    while len > 0
        sons = collect(SatMachine.map_get_node(GMAP[], k).sons)
        isempty(sons) && break
        k = sons[rand(RNG[], 1:length(sons))]
        append!(R, collect(SatMachine.map_get_node(GMAP[], k).requires))
        len -= 1
    end
    return unique(R)
end
pin(g, R) = (h = deepcopy(g); h.review_owners = true; GraphPath.filter!(h, SetNodesId(R)); h)

function live_parents(g, x, chain)
    nd = PathCollectionLines.get_node(g.table_lines, x)
    nd === nothing && return PathNodeId[]
    [p for p in nd.parents if PG.is_alive(g.og, p) && all(w -> adj(g, w, p), chain) &&
        !any(dead(g, chain[i], chain[j], p) for i in eachindex(chain) for j in i+1:length(chain))]
end

# ¿el último nodo de la cadena la mantiene viva en el lado s? devuelve :ok o el primer motivo de fallo
function step_side(s, chain)
    s.is_valid || return :invalid
    x = chain[end]; k = length(chain)
    PG.is_alive(s.og, x) || return :node
    all(w -> adj(s, w, x), chain) || return :edge
    if k >= 2
        nd = PathCollectionLines.get_node(s.table_lines, chain[end-1])
        (nd === nothing || !(x in nd.parents)) && return :link
    end
    for i in 1:k-1, j in i+1:k-1
        a, b = chain[i], chain[j]
        (dead(s, a, b, x) || dead(s, a, x, b) || dead(s, b, x, a)) && return :trio
    end
    return :ok
end

function dead_ends(g)
    g.is_valid || return 0
    top = Int(g.current_step) - 1
    leaves = Ref(0); deads = Ref(0)
    chain = PathNodeId[]
    function dfs(x)
        (leaves[] > CAP || !ram_ok()) && return
        push!(chain, x)
        if Int(x.id.step) == 0
            leaves[] += 1
        else
            ps = live_parents(g, x, chain)
            isempty(ps) ? (deads[] += 1) : foreach(dfs, ps)
        end
        pop!(chain)
    end
    foreach(dfs, alive_at(g, top))
    return deads[]
end

function judge_pinned(U, PA, PB)
    U.is_valid || return
    bump(:runs)
    bump(:side_dead, dead_ends(PA) + dead_ends(PB))
    top = Int(U.current_step) - 1
    leaves = Ref(0)
    chain = PathNodeId[]
    # ra, rb: estado de la cadena en cada lado (:ok o el primer motivo); tside: lado de la cima (1, 2 o 0)
    function dfs(x, ra, rb, tside)
        (leaves[] > CAP || !ram_ok()) && return
        push!(chain, x)
        ra == :ok && (ra = step_side(PA, chain))
        rb == :ok && (rb = step_side(PB, chain))
        if length(chain) == 1
            tside = ra == :ok ? 1 : (rb == :ok ? 2 : (PG.is_alive(PA.og, x) ? 1 : (PG.is_alive(PB.og, x) ? 2 : 0)))
        end
        bump(:chains)
        if ra != :ok && rb != :ok
            bump(:none)
            why = tside == 2 ? rb : ra
            bump(Symbol("n_", why))
        elseif ra == :ok && rb == :ok
            bump(:both)
        end
        if Int(x.id.step) == 0
            leaves[] += 1
        else
            ps = live_parents(U, x, chain)
            isempty(ps) ? bump(:dead) : foreach(p -> dfs(p, ra, rb, tside), ps)
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, :ok, :ok, 0), alive_at(U, top))
    leaves[] > CAP && bump(:cap)
end

function judge(u, a, b)
    u.is_valid || return
    bump(:joins)
    Rs = Any[NodeId[]]
    for _ in 1:SAMPLES
        R = PIN_MODE == "real" ? real_pins(u.map_parent_id) : random_pins(u, rand(RNG[], 1:3))
        (isempty(R) || R in Rs) || push!(Rs, R)
    end
    for R in Rs
        ram_ok() || (bump(:ram); return)
        judge_pinned(pin(u, R), pin(a, R), pin(b, R))
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :runs, :chains, :none, :both, :n_invalid, :n_node, :n_edge, :n_link, :n_trio, :dead, :side_dead,
            :cap, :ram)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            GMAP[] = machine.gmap
            Probes.with(:join_pre => (a, b) -> (PRE[] = (deepcopy(a), deepcopy(b))),
                        :join_post => u -> (PRE[] === nothing || judge(deepcopy(u), PRE[]...); PRE[] = nothing)) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
