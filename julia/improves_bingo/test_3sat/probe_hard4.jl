# El caso abierto de cuatro bloques (3-oct-2026, rama reader-stuck; Lean ForbidOnChain4.lean).
#
#   PROBE_MAP=bin PROBE_DIRS=../../lean/improves_bingo/scripts/cnf PROBE_ONLY=chain4_cross.cnf HARD4_CHAIN=chain4_cross \
#     test_3sat/run_capped.sh 3500 6000 julia --heap-size-hint=3G --project=. test_3sat/probe_hard4.jl <salida.tsv>
#
# Con FORBID = :on. Bloques `A ∪ {s1}`, `{s1} ∪ M ∪ {s2}`, `{s2} ∪ N ∪ {s3}`, `{s3} ∪ C` (HARD4_CHAIN elige los datos).
# Con la variable fijada `v` dentro de un bloque, la prueba de Lean se atasca en un triángulo que no lee ningún
# separador y en el que, para cada separador, algún lado (sin `v`) tiene una variable leída solo por la ventana de
# cada uno de los tres nodos (`fails`): entonces ninguna cara de un testigo cubre ese lado. Esto es una condición
# necesaria del atasco (que las caras discrepen de verdad depende de sus ramas), medida en los estados de la máquina:
#   <g>_states      estados juzgados (g = flt: tras el filtro del UP, σ = paso del requisito; arr: llegada, σ = cima;
#                   jrev: unión revisada; fin: estado final)
#   <g>_t           triángulos sin prohibir de nodos vivos
#   <g>_nosep       los que no leen ningún separador
#   <g>_hard_sigma  los difíciles para la variable de σ (solo flt y arr, si es interior); `_T<n>`: en la línea n
#                   (el estado tiene los pasos 0 … n - 1; las familias exigen las ventanas por debajo de n)
#   <g>_hard_any    los difíciles para alguna variable interior
#   <g>_hard_<v>    los difíciles para la variable interior v

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
const CHAINS = Dict(
    "chain4_cross" => (A = [1, 3], s1 = 6, M = [5], s2 = 7, N = [2], s3 = 8, Cc = [4, 9]),
)
const CH = CHAINS[get(ENV, "HARD4_CHAIN", "chain4_cross")]
const SEPS = [CH.s1, CH.s2, CH.s3]
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

function judge(g, pre; sigmas = Int[])
    g.is_valid || return
    og = g.og
    top = Int(g.current_step) - 1
    top >= 2 || return
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    bump(Symbol(pre, "_states"))
    svars = [step_var(σ) for σ in sigmas]
    svars = [z for z in svars if z in INTERIOR]
    for sa in 0:top, a in alive[sa]
        for sb in (sa + 1):top, b in PG.neighbors(og, a, Step(sb))
            PG.is_alive(og, b) || continue
            for sr in (sb + 1):top, r in PG.neighbors(og, a, Step(sr))
                (PG.is_alive(og, r) && PG.has_edge(og, b, r)) || continue
                PG.dead_trio(og, a, b, r) && continue
                bump(Symbol(pre, "_t"))
                Wa, Wb, Wr = win(sa), win(sb), win(sr)
                any(s -> s in Wa || s in Wb || s in Wr, SEPS) && continue
                bump(Symbol(pre, "_nosep"))
                P = (setdiff(Wa, Wb, Wr), setdiff(Wb, Wa, Wr), setdiff(Wr, Wa, Wb))
                if any(v -> hard_for(v, P), svars)
                    bump(Symbol(pre, "_hard_sigma"))
                    bump(Symbol(pre, "_hard_sigma_T", top + 1))
                end
                hv = [v for v in INTERIOR if hard_for(v, P)]
                isempty(hv) || bump(Symbol(pre, "_hard_any"))
                foreach(v -> bump(Symbol(pre, "_hard_", v)), hv)
            end
        end
    end
    dump_partial()
end

Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        $(judge)(gpath, "flt"; sigmas = [Int(r.step) for r in requires])
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

function reviewed(g)
    h = deepcopy(g)
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    groups = ("flt", "arr", "jrev", "fin")
    fields = vcat(["states", "t", "nosep", "hard_sigma", "hard_any"], ["hard_$v" for v in INTERIOR])
    cols = [Symbol(g, "_", f) for g in groups for f in fields]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus()) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        load_cnf(path)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            Probes.with(:up_done => g -> judge(g, "arr"; sigmas = [Int(g.current_step) - 1]),
                        :join_post => g -> judge(reviewed(g), "jrev")) do
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
