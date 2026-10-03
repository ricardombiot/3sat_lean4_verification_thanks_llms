# El caso abierto de cinco bloques en el lector (3-oct-2026, rama reader-stuck). Como probe_hard4_read.jl, para
# `chain5_cross` y `v` en el último bloque `C`: rd_dbl cuenta los triángulos sin separadores leídos en los que cada
# nodo lee solo en su ventana una variable de `A ∪ M1` y otra de `M2 ∪ M3 ∪ C∖{v}` (las dos elecciones de testigo de
# ventana fallan); rd_dbl_out, los que están fuera de toda camarilla.
#
#   PROBE_MAP=bin PROBE_DIRS=../../lean/improves_bingo/scripts/cnf PROBE_ONLY=chain4_cross.cnf HARD4_CHAIN=chain4_cross \
#     test_3sat/run_capped.sh 3500 6000 julia --heap-size-hint=3G --project=. test_3sat/probe_hard4_read.jl <salida.tsv>
#
# Con FORBID = :on. Desde cada estado final (revisado), lecturas como Lean `Reading`: fijar un nodo vivo (paso ≥ 1) y
# revisar, repetido. Todas las lecturas de un paso, y READ_N lecturas aleatorias de hasta READ_LEN pasos (semilla
# READ_SEED). En cada estado leído, con σ = paso del último nodo fijado (la estructura de `HRead`):
#   rd_states / rd_invalid   estados leídos / leídos que quedaron inválidos (el lector se atasca)
#   rd_cap                   estados con más de EXACT_CAP camarillas (sin juzgar)
#   rd_t                     triángulos sin prohibir (aquí no se juzga la exactitud de todos: solo rd_dbl_out)
#   rd_nosep                 los que no leen ningún separador
#   rd_hard_sigma            los difíciles para la variable de σ (si es interior), como en probe_hard4.jl
#   rd_hard_sigma_out        de ellos, fuera de toda camarilla
#   rd_hard_sigma_<v>        por variable fijada
using Random
const OUT = abspath(ARGS[1])
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

# Datos de la cadena (variables 1-indexadas, como en el .cnf).
const CHAINS5 = Dict("chain5_cross" => (A = [1, 3], M1 = [5], M2 = [2], M3 = [4], Cc = [10, 11], seps = [6, 7, 8, 9]))
const CH5 = CHAINS5["chain5_cross"]
const CHAINS = Dict(
    "chain5_cross" => (A = [1, 3], s1 = 6, M = [5], s2 = 7, N = [2], s3 = 8, Cc = [4, 9]),
    "chain4_cross" => (A = [1, 3], s1 = 6, M = [5], s2 = 7, N = [2], s3 = 8, Cc = [4, 9]),
    "chain4_l" => (A = [1, 3], s1 = 6, M = [5], s2 = 7, N = [2], s3 = 8, Cc = [4, 9]),
)
const CH = CHAINS[get(ENV, "HARD4_CHAIN", "chain4_cross")]
const SEPS = CH5.seps
const INTERIOR = vcat(CH.A, CH.M, CH.N, CH.Cc)
# los lados de cada separador, sin separadores
const SIDES = [(CH.A, vcat(CH.M, CH.N, CH.Cc)), (vcat(CH.A, CH.M), vcat(CH.N, CH.Cc)), (vcat(CH.A, CH.M, CH.N), CH.Cc)]

# La fórmula, para saber qué variable lee cada paso.
const NV = Ref(0)
const CLAUSES = Ref(Vector{Vector{Int}}())
function load_cnf(path)
    cls = Vector{Vector{Int}}()
    for line in eachline(path)
        s = strip(line)
        (isempty(s) || s[1] in ('c', '%')) && continue
        if s[1] == 'p'
            NV[] = parse(Int, split(s)[3]); continue
        end
        lits = [parse(Int, t) for t in split(s) if t != "0"]
        isempty(lits) || push!(cls, abs.(lits))
    end
    CLAUSES[] = cls
end

# La variable que lee el paso k (Lean `stepVar`), o 0.
function step_var(k)
    n = NV[]
    1 <= k <= 2n && return (k + 1) ÷ 2
    o = k - 2n - 2
    (o < 0 || o >= 3 * length(CLAUSES[])) && return 0
    return CLAUSES[][o ÷ 3 + 1][o % 3 + 1]
end

# Las variables que lee la ventana del paso k (Lean `InWin`: k, k-1, k-2).
function win(k)
    s = Set{Int}()
    for k2 in (k, k - 1, k - 2)
        k2 >= 0 || continue
        z = step_var(k2); z == 0 || push!(s, z)
    end
    return s
end

fails(P, S) = all(p -> any(z -> z in S, p), P)

function hard_for(v, P)
    all(j -> fails(P, setdiff(SIDES[j][1], [v])) || fails(P, setdiff(SIDES[j][2], [v])), 1:3)
end


const CAP = parse(Int, get(ENV, "EXACT_CAP", "50000"))
const READ_N = parse(Int, get(ENV, "READ_N", "300"))
const READ_LEN = parse(Int, get(ENV, "READ_LEN", "4"))
const READ_SEED = parse(Int, get(ENV, "READ_SEED", "1"))

# Los triángulos de las camarillas del estado (cadenas de vivos de la cima al paso 0, vecinos dos a dos, sin tríos
# muertos), o `nothing` si pasan del tope.
function clique_trios(g, top, alive)
    og = g.og
    T = Set{NTuple{3, PathNodeId}}()
    cliq = Ref(0); chain = PathNodeId[]
    ok(p) = all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        cliq[] > CAP && return
        push!(chain, x)
        if s == 0
            cliq[] += 1
            L = length(chain)
            for i in 1:L, j in (i + 1):L, k in (j + 1):L
                push!(T, (chain[k], chain[j], chain[i]))
            end
        else
            foreach(p -> dfs(p, s - 1), [p for p in alive[s - 1] if ok(p)])
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, top), alive[top])
    return cliq[] > CAP ? nothing : T
end

function judge_read(g, σ)
    bump(:rd_states)
    if !g.is_valid
        bump(:rd_invalid); return
    end
    og = g.og
    top = Int(g.current_step) - 1
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    # las camarillas solo si hace falta (algún triángulo de la configuración doble)
    Tref = Ref{Any}(missing)
    getT() = (Tref[] === missing && (Tref[] = clique_trios(g, top, alive)); Tref[])
    sv = step_var(σ)
    vint = sv in INTERIOR
    for sa in 0:top, a in alive[sa]
        for sb in (sa + 1):top, b in PG.neighbors(og, a, Step(sb))
            PG.is_alive(og, b) || continue
            for sr in (sb + 1):top, r in PG.neighbors(og, a, Step(sr))
                (PG.is_alive(og, r) && PG.has_edge(og, b, r)) || continue
                PG.dead_trio(og, a, b, r) && continue
                bump(:rd_t)
                Wa, Wb, Wr = win(sa), win(sb), win(sr)
                any(s -> s in Wa || s in Wb || s in Wr, SEPS) && continue
                bump(:rd_nosep)
                sv in CH5.Cc || continue
                P = (setdiff(Wa, Wb, Wr), setdiff(Wb, Wa, Wr), setdiff(Wr, Wa, Wb))
                L = vcat(CH5.A, CH5.M1); R = setdiff(vcat(CH5.M2, CH5.M3, CH5.Cc), [sv])
                if fails(P, L) && fails(P, R)
                    bump(:rd_dbl); bump(Symbol(:rd_dbl_, sv))
                    T = getT()
                    T === nothing ? bump(:rd_cap) : ((a, b, r) in T || bump(:rd_dbl_out))
                end
            end
        end
    end
    dump_partial()
end

function reviewed(g)
    h = deepcopy(g)
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

# Fijar un nodo y revisar (Lean `filterAllOn [q.id]`).
function pin(g, q)
    h = deepcopy(g)
    h.review_owners = true
    GraphPath.filter!(h, SetNodesId([q.id]))
    return h
end

alive_nodes(g) = [q for s in 1:(Int(g.current_step) - 1) for q in get(g.og.alive, Step(s), SetPathNodesId())]

function read_all(g0)
    for q in alive_nodes(g0)
        judge_read(pin(g0, q), Int(q.id.step))
    end
    rng = MersenneTwister(READ_SEED)
    for _ in 1:READ_N
        g = g0
        for _ in 1:rand(rng, 2:READ_LEN)
            g.is_valid || break
            qs = alive_nodes(g)
            isempty(qs) && break
            q = qs[rand(rng, 1:length(qs))]
            g = pin(g, q)
            judge_read(g, Int(q.id.step))
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    fields = ["states", "invalid", "cap", "t", "t_out", "nosep", "dbl", "dbl_out", "dbl_10", "dbl_11"]
    cols = [Symbol("rd_", f) for f in fields]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus()) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        load_cnf(path)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            if SatMachine.have_solution(machine)
                for g in SatMachine.get_gpath_solutions(machine)
                    read_all(reviewed(g))
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
