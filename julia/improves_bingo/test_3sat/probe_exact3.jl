# Exactitud por niveles en TODOS los estados (1-oct-2026, rama reader-stuck; tras el v220).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_exact3.jl <salida.tsv>
#
# Con FORBID = :on. In_k: todo k-conjunto «vivo de cerca» del estado está en alguna camarilla (un vivo por paso, vecinos
# dos a dos, sin trío prohibido): k = 1 nodos vivos, k = 2 aristas vivas, k = 3 triángulos vivos sin prohibir.
# Se enumeran todas las camarillas del estado (DFS de la cima hacia abajo, todos los candidatos; tope EXACT_CAP: un
# estado que lo alcanza cuenta en `cap` y no se juzga) y se compara con los nodos, aristas y triángulos del grafo.
#   flt_*   remitentes tras el filtro de requisitos de cada llegada, antes de la fila nueva: el estado de la hipótesis
#           Lean `HypsTriFlt` (ForbidOnExact.lean): `TopTri (kv.2.filterAllOn (reqOf φ d))`
#   arr_*   llegadas (tras el UP y su review, punto :up_done)
#   jrev_*  uniones tras una revisión (lo que ve el siguiente UP)
#   fin_*   estados finales revisados
# Tras cada estado juzgado se vuelcan los contadores a <salida>.partial (una sonda larga no pierde lo medido).
# Por grupo: states, cap, cliq (camarillas, máximo de un estado), dead (callejones del DFS), n / n_out (nodos vivos /
# fuera de toda camarilla), e / e_out (aristas), t / t_out (triángulos sin prohibir), tt / tt_out (los triángulos con
# un nodo en la cima: Lean `TopTri`; con `te / te_out`, las aristas de cima: `TopEdge`).
# Solo en flt, con el requisito r de la llegada (paso σ): tt_free (triángulos de cima con un nodo en σ: no piden nada),
# q (tetraedros de Lean `PinTetra`: triángulo de cima sin prohibir + nodo s de σ vecino de los tres, con las tres caras
# con s sin prohibir) y q_dead (los que no están en ninguna camarilla: si tt_out = 0, su triángulo de cima se salva por
# otro nodo de σ).

const OUT = abspath(ARGS[1])
const CAP = parse(Int, get(ENV, "EXACT_CAP", "50000"))
# EXACT_LINKS=1: la camarilla además sigue los enlaces de documentos (cada nodo es padre del anterior), como Lean
# `Carried.node`. Sin ella solo se pide vecindad dos a dos y ningún trío prohibido.
const LINKS = get(ENV, "EXACT_LINKS", "0") == "1"
# EXACT_GROUPS=flt,fin: solo se juzgan esos grupos (instancias grandes: flt es el estado de la hipótesis).
const GROUPS = Set(split(get(ENV, "EXACT_GROUPS", "flt,arr,jrev,fin"), ","; keepempty = false))
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

function reviewed(g)
    h = deepcopy(g)
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

function judge(g, pre; reqs = nothing)
    g.is_valid || return
    string(pre) in GROUPS || return
    og = g.og
    top = Int(g.current_step) - 1
    top >= 2 || return
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    bump(Symbol(pre, "_states"))
    # camarillas
    N = Set{PathNodeId}(); E = Set{NTuple{2, PathNodeId}}(); T = Set{NTuple{3, PathNodeId}}()
    sigmas = reqs === nothing ? Int[] : [Int(r.step) for r in reqs if 0 <= Int(r.step) <= top]
    Q = Dict{NTuple{3, PathNodeId}, Set{PathNodeId}}()     # triángulo de cima => nodos de σ de sus camarillas
    cliq = Ref(0); deads = Ref(0); chain = PathNodeId[]
    linked(p) = !LINKS || (nd = PathCollectionLines.get_node(g.table_lines, chain[end]); nd !== nothing && p in nd.parents)
    ok(p) = linked(p) && all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        cliq[] > CAP && return
        push!(chain, x)
        if s == 0
            cliq[] += 1
            L = length(chain)          # chain va de la cima al paso 0: pasos decrecientes
            for i in 1:L
                push!(N, chain[i])
                for j in (i + 1):L
                    push!(E, (chain[j], chain[i]))
                    for k in (j + 1):L
                        push!(T, (chain[k], chain[j], chain[i]))
                        if i == 1
                            for σ in sigmas
                                push!(get!(() -> Set{PathNodeId}(), Q, (chain[k], chain[j], chain[1])), chain[top - σ + 1])
                            end
                        end
                    end
                end
            end
        else
            cs = [p for p in alive[s - 1] if ok(p)]
            isempty(cs) ? (deads[] += 1) : foreach(p -> dfs(p, s - 1), cs)
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, top), alive[top])
    if cliq[] > CAP
        bump(Symbol(pre, "_cap")); return
    end
    C[Symbol(pre, "_cliq")] = max(get(C, Symbol(pre, "_cliq"), 0), cliq[])
    bump(Symbol(pre, "_dead"), deads[])
    # el grafo: nodos, aristas y triángulos sin prohibir, con pasos crecientes (a < b < r)
    for sa in 0:top, a in alive[sa]
        bump(Symbol(pre, "_n")); a in N || bump(Symbol(pre, "_n_out"))
        for sb in (sa + 1):top, b in PG.neighbors(og, a, Step(sb))
            PG.is_alive(og, b) || continue
            bump(Symbol(pre, "_e")); (a, b) in E || bump(Symbol(pre, "_e_out"))
            if sb == top
                bump(Symbol(pre, "_te")); (a, b) in E || bump(Symbol(pre, "_te_out"))
            end
            for sr in (sb + 1):top, r in PG.neighbors(og, a, Step(sr))
                (PG.is_alive(og, r) && PG.has_edge(og, b, r)) || continue
                PG.dead_trio(og, a, b, r) && continue
                bump(Symbol(pre, "_t")); (a, b, r) in T || bump(Symbol(pre, "_t_out"))
                if sr == top
                    bump(Symbol(pre, "_tt")); (a, b, r) in T || bump(Symbol(pre, "_tt_out"))
                    for σ in sigmas
                        if σ == sa || σ == sb || σ == sr
                            bump(Symbol(pre, "_tt_free")); continue
                        end
                        inq = get(Q, (a, b, r), nothing)
                        for x in PG.neighbors(og, a, Step(σ))
                            (PG.is_alive(og, x) && PG.has_edge(og, b, x) && PG.has_edge(og, r, x)) || continue
                            (PG.dead_trio(og, a, b, x) || PG.dead_trio(og, a, r, x) || PG.dead_trio(og, b, r, x)) && continue
                            bump(Symbol(pre, "_q"))
                            (inq !== nothing && x in inq) || bump(Symbol(pre, "_q_dead"))
                        end
                    end
                end
            end
        end
    end
    dump_partial()
end

# Tras el filtro de requisitos del UP (antes de la fila nueva).
Core.eval(GraphPath, quote
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        gpath.map_parent_id === nothing || PathOwnersGraph.stamp!(gpath.og, gpath.map_parent_id)
        filter!(gpath, requires)
        $(judge)(gpath, "flt"; reqs = requires)
        do_up!(gpath, map_id_node, title, prohibited)
    end
end)

function main()
    _, loader, _ = ProbeLib.map_of_env()
    groups = ("flt", "arr", "jrev", "fin")
    fields = ("states", "cap", "cliq", "dead", "n", "n_out", "e", "e_out", "t", "t_out", "te", "te_out", "tt", "tt_out", "tt_free", "q", "q_dead")
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
            Probes.with(:up_done => g -> judge(g, "arr"), :join_post => g -> judge(reviewed(g), "jrev")) do
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
