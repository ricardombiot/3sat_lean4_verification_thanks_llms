# Sonda del enlace (4-oct-2026, rama reader-stuck; Lean `ForbidOnLink.lean`).
#
#   PROBE_MAP=bin PROBE_ONLY=chain4_cross.cnf,... julia --project=. test_3sat/probe_link.jl <salida.tsv>
#
# `LinkB3` en los pasos de los separadores: para cada estado juzgado (como `probe_exact3.jl`: flt, arr, jrev, fin) y
# cada nodo vivo `n` en un paso de un separador (variable en dos cláusulas o más; pasos binarios 2v-1, 2v), los
# tetraedros `(a, b, r, n)` con todas sus aristas vivas y sus cuatro caras sin prohibir (`lb3_t`), y los que no están en
# ninguna camarilla (`lb3_dead`: el tetraedro no es de ninguna rama, `LinkB3` falla en `n`). Si `lb3_dead = 0`,
# también vale `LinkTrio` (la camarilla da en cada paso un nodo que completa el tetraedro). `lb3_nodes`: nodos `n`
# examinados; `lb3_bad_nodes`: los que tienen algún tetraedro muerto. Igual con `σ` (el paso del requisito, solo en
# flt) como contraste: `sg_t`, `sg_dead`.

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
const SEPSTEPS = Ref(Int[])
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
    CL = Vector{Set{PathNodeId}}()
    linked(p) = !LINKS || (nd = PathCollectionLines.get_node(g.table_lines, chain[end]); nd !== nothing && p in nd.parents)
    ok(p) = linked(p) && all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        cliq[] > CAP && return
        push!(chain, x)
        if s == 0
            cliq[] += 1
            push!(CL, Set(chain))
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
    # el enlace: tetraedros con un nodo de un paso de separador (o de σ)
    idx = Dict{PathNodeId, Vector{Int}}()
    for (ci, c) in enumerate(CL), p in c
        push!(get!(() -> Int[], idx, p), ci)
    end
    function tetra(n, lab)
        λ = Int(n.id.step)
        nb = PathNodeId[]
        for s in 0:top
            s == λ && continue
            for x in PG.neighbors(og, n, Step(s))
                PG.is_alive(og, x) && push!(nb, x)
            end
        end
        sort!(nb, by = x -> Int(x.id.step))
        cs = get(idx, n, Int[])
        bad = false
        for ia in eachindex(nb), ib in (ia + 1):length(nb)
            a = nb[ia]; b = nb[ib]
            Int(a.id.step) == Int(b.id.step) && continue
            PG.has_edge(og, a, b) || continue
            PG.dead_trio(og, a, b, n) && continue
            for ir in (ib + 1):length(nb)
                r = nb[ir]
                Int(r.id.step) == Int(b.id.step) && continue
                (PG.has_edge(og, a, r) && PG.has_edge(og, b, r)) || continue
                (PG.dead_trio(og, a, r, n) || PG.dead_trio(og, b, r, n) || PG.dead_trio(og, a, b, r)) && continue
                bump(Symbol(pre, "_", lab, "_t"))
                if !any(ci -> (a in CL[ci] && b in CL[ci] && r in CL[ci]), cs)
                    bump(Symbol(pre, "_", lab, "_dead")); bad = true
                end
            end
        end
        return bad
    end
    for λ in SEPSTEPS[]
        λ <= top || continue
        for n in alive[λ]
            bump(Symbol(pre, "_lb3_nodes"))
            tetra(n, "lb3") && bump(Symbol(pre, "_lb3_bad_nodes"))
        end
    end
    for σ in sigmas, n in alive[σ]
        tetra(n, "sg")
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
    fields = ("states", "cap", "cliq", "lb3_nodes", "lb3_bad_nodes", "lb3_t", "lb3_dead", "sg_t", "sg_dead")
    cols = [Symbol(g, "_", f) for g in groups for f in fields]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        cls = [filter(!=(0), parse.(Int, split(l))) for l in eachline(path) if !isempty(strip(l)) && !(strip(l)[1] in ('c', 'p', '%'))]
        occ = Dict{Int, Int}()
        for c in cls, v in unique(abs.(c))
            occ[v] = get(occ, v, 0) + 1
        end
        seps = sort([v for (v, k) in occ if k >= 2])
        SEPSTEPS[] = sort(vcat([2v - 1 for v in seps], [2v for v in seps]))
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
