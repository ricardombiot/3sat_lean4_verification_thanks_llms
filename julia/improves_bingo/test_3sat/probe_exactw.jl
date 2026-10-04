# Exactitud de las llegadas hacia la unión (2-oct-2026, rama reader-stuck): la medida de Lean `MachineExactW`
# (ForbidOnWeak.lean).
#
#   PROBE_MAP=bin PROBE_DIRS=../../lean/improves_bingo/scripts/cnf PROBE_ONLY=chain6_cross.cnf \
#     test_3sat/run_capped.sh 3500 6000 julia --heap-size-hint=3G --project=. test_3sat/probe_exactw.jl <salida.tsv>
#
# Con FORBID = :on. `MachineExactW` pide a cada llegada válida `k → d` que sus parejas de vecinos y sus triángulos sin
# prohibir sean de ramas de soluciones que eligen `d` (las de la entrada que la llegada va a formar), vengan del
# remitente que vengan. Las ramas de esas soluciones son las camarillas de las llegadas a `d` de la misma línea (a lo
# sumo dos en el mapa bin), así que cada llegada se compara con sus camarillas y con las de su hermana:
#   arr_states          llegadas válidas juzgadas (cap: las que pasan de EXACT_CAP camarillas, sin juzgar)
#   arr_e / arr_t       parejas de vecinos / triángulos sin prohibir de las llegadas
#   arr_e_own / arr_t_own   los que no están en ninguna camarilla de la propia llegada (lo que mide `probe_exact3.jl`
#                           como `arr_e_out` / `arr_t_out`; `MachineExact` pide 0)
#   arr_e_w / arr_t_w   los que tampoco están en ninguna camarilla de la hermana (`MachineExactW` pide 0)
#   arr_pairs / arr_single  llegadas con hermana / sin hermana (la hermana no existe, no es válida o pasó el tope)
#   arr_third           llegadas a una entrada que ya tenía dos (no debería haber: 0)

const OUT = abspath(ARGS[1])
const CAP = parse(Int, get(ENV, "EXACT_CAP", "50000"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
dump_partial() = open(OUT * ".partial", "w") do io
    for k in sort(collect(keys(C)), by = string)
        println(io, k, "\t", C[k])
    end
end

const P2 = NTuple{2, PathNodeId}
const P3 = NTuple{3, PathNodeId}
# (cima, d) => (parejas y triángulos de camarillas de la primera llegada, sus objetos fuera de sus camarillas)
const SIB = Dict{Tuple{Int, NodeId}, Tuple{Set{P2}, Set{P3}, Vector{P2}, Vector{P3}}}()
const SEEN = Dict{Tuple{Int, NodeId}, Int}()

# Una llegada sin hermana: lo que no está en sus camarillas no está en ninguna.
function close_single!(key)
    _, _, oe, ot = SIB[key]
    bump(:arr_single); bump(:arr_e_w, length(oe)); bump(:arr_t_w, length(ot))
    delete!(SIB, key)
end

function judge(g)
    g.is_valid || return
    og = g.og
    top = Int(g.current_step) - 1
    top >= 2 || return
    # la línea anterior ya no recibe más llegadas
    for key in collect(keys(SIB))
        key[1] < top && close_single!(key)
    end
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    isempty(alive[top]) && return
    key = (top, first(alive[top]).id)
    bump(:arr_states)
    E = Set{P2}(); T = Set{P3}()
    cliq = Ref(0); chain = PathNodeId[]
    ok(p) = all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        cliq[] > CAP && return
        push!(chain, x)
        if s == 0
            cliq[] += 1
            L = length(chain)          # chain va de la cima al paso 0: pasos decrecientes
            for i in 1:L, j in (i + 1):L
                push!(E, (chain[j], chain[i]))
                for k in (j + 1):L
                    push!(T, (chain[k], chain[j], chain[i]))
                end
            end
        else
            foreach(p -> dfs(p, s - 1), [p for p in alive[s - 1] if ok(p)])
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, top), alive[top])
    if cliq[] > CAP
        bump(:arr_cap); return
    end
    oe = P2[]; ot = P3[]
    for sa in 0:top, a in alive[sa]
        for sb in (sa + 1):top, b in PG.neighbors(og, a, Step(sb))
            PG.is_alive(og, b) || continue
            bump(:arr_e); (a, b) in E || push!(oe, (a, b))
            for sr in (sb + 1):top, r in PG.neighbors(og, a, Step(sr))
                (PG.is_alive(og, r) && PG.has_edge(og, b, r)) || continue
                PG.dead_trio(og, a, b, r) && continue
                bump(:arr_t); (a, b, r) in T || push!(ot, (a, b, r))
            end
        end
    end
    bump(:arr_e_own, length(oe)); bump(:arr_t_own, length(ot))
    SEEN[key] = get(SEEN, key, 0) + 1
    if SEEN[key] > 2
        bump(:arr_third)
    elseif haskey(SIB, key)
        E1, T1, oe1, ot1 = SIB[key]
        bump(:arr_pairs, 2)
        bump(:arr_e_w, count(x -> !(x in E1), oe) + count(x -> !(x in E), oe1))
        bump(:arr_t_w, count(x -> !(x in T1), ot) + count(x -> !(x in T), ot1))
        delete!(SIB, key)
    else
        SIB[key] = (E, T, oe, ot)
    end
    dump_partial()
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = [:arr_states, :arr_cap, :arr_e, :arr_e_own, :arr_e_w, :arr_t, :arr_t_own, :arr_t_w, :arr_pairs, :arr_single,
            :arr_third]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(dirs = String[])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(SIB); empty!(SEEN)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            Probes.with(:up_done => judge) do
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            end
            foreach(close_single!, collect(keys(SIB)))
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
