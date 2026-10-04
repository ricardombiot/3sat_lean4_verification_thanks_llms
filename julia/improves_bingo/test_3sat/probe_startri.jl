# "El primero que muere" en la estrella de la cima (1-oct-2026, rama reader-stuck).
#
#   PIN_MODE=random|real PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_startri.jl <salida.tsv> [muestras]
#
# Con FORBID = :on. En cada join, para R = [] y pins R: U = pin(join(A,B), R). Para cada cima viva t de U, con S el
# lado donde t está viva y P = pin(S, R), la FAMILIA de t en U:
#   nodos    — t y sus vecinos en U
#   aristas  — t–y, y las y–w entre vecinos con el trío (t, y, w) sin prohibir en U
#   tríos    — los (t, y, w) de esas aristas
# M1 (la familia sobrevive en el lado fijado): m1_node, m1_tedge, m1_edge (falta en P), m1_trio (prohibido en P);
#   fam_nodes, fam_edges de tamaño.
# M2 (StarTri, lo que el argumento necesita): para cada arista y–w de la familia y cada paso l por debajo de la cima
#   (que no sea el de y ni el de w), un testigo bueno de (t, y, w) en U — s vecino de t, y, w con (t,y,s), (t,w,s) y
#   (y,w,s) sin prohibir en U — cuyo trío (y, w, s) no esté prohibido en P.
#   m2_cells, m2_nowit (sin testigo en U: el punto fijo dice 0), m2_fail (ningún testigo con (y,w,s) triángulo sin
#   prohibir de P), m2_fail_len (ninguno, contando como bueno el que tiene una arista de menos en P).
# M3 (todos los testigos): m3_wit, m3_dead (triángulo de P prohibido), m3_missing (falta una arista en P),
#   m3_deadS (prohibido en el lado sin fijar).
# consec_fail: aristas de U entre pasos consecutivos cuyo nodo de abajo no es padre (documento) del de arriba.

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 2
const RAM_MB = parse(Int, get(ENV, "PROBE_RAM_MB", "3500"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(20261001))
const PRE = Ref{Any}(nothing)
const PIN_MODE = get(ENV, "PIN_MODE", "random")
const GMAP = Ref{Any}(nothing)

ram_ok() = Sys.maxrss() / 2^20 < RAM_MB
alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
edge(g, a, b) = PG.has_edge(g.og, a, b)
dead(g, a, b, r) = PG.has_edge(g.og, a, b) && PG.dead_trio(g.og, a, b, r)
st(x) = Int(x.id.step)

function random_pins(g, n)
    top = Int(g.current_step) - 1
    steps = [s for s in 1:top-1 if length(unique(x.id for x in alive_at(g, s))) >= 2]
    isempty(steps) && return NodeId[]
    [begin ids = unique(x.id for x in alive_at(g, s)); ids[rand(RNG[], 1:length(ids))] end
     for s in shuffle(RNG[], steps)[1:min(n, length(steps))]]
end
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

function consec(U)
    for (k, e) in U.og.edges
        abs(st(e.a) - st(e.b)) == 1 || continue
        hi, lo = st(e.a) > st(e.b) ? (e.a, e.b) : (e.b, e.a)
        nd = PathCollectionLines.get_node(U.table_lines, hi)
        (nd !== nothing && lo in nd.parents) || bump(:consec_fail)
    end
end

function judge_top(U, t, S, P)
    top = st(t)
    N = [y for y in collect(PG.neighbors_all(U.og, t)) if y != t && PG.is_alive(U.og, y)]
    bump(:fam_nodes, length(N))
    pv = P.is_valid
    pv || bump(:p_invalid)
    for y in N
        (pv && PG.is_alive(P.og, y)) || bump(:m1_node)
        (pv && edge(P, t, y)) || bump(:m1_tedge)
    end
    bystep = Dict{Int, Vector{PathNodeId}}()
    for y in N
        push!(get!(bystep, st(y), PathNodeId[]), y)
    end
    for i in eachindex(N), j in i+1:length(N)
        y, w = N[i], N[j]
        (edge(U, y, w) && !dead(U, t, y, w)) || continue
        bump(:fam_edges)
        (pv && edge(P, y, w)) || bump(:m1_edge)
        (pv && edge(P, t, y) && dead(P, t, y, w)) && bump(:m1_trio)
        for l in 0:top-1
            (l == st(y) || l == st(w)) && continue
            bump(:m2_cells)
            anyw = false; ok = false; oklen = false
            for s in get(bystep, l, PathNodeId[])
                (edge(U, y, s) && edge(U, w, s)) || continue
                (dead(U, t, y, s) || dead(U, t, w, s) || dead(U, y, w, s)) && continue
                anyw = true
                bump(:m3_wit)
                full = pv && edge(P, y, w) && edge(P, y, s) && edge(P, w, s)
                dP = full && PG.dead_trio(P.og, y, w, s)
                full || bump(:m3_missing)
                dP && bump(:m3_dead)
                (edge(S, y, w) && edge(S, y, s) && edge(S, w, s) && PG.dead_trio(S.og, y, w, s)) && bump(:m3_deadS)
                (full && !dP) && (ok = true)
                dP || (oklen = true)
            end
            anyw || bump(:m2_nowit)
            ok || bump(:m2_fail)
            oklen || bump(:m2_fail_len)
        end
    end
end

function judge(u, a, b)
    u.is_valid || return
    bump(:joins)
    Rs = Any[NodeId[]]
    for _ in 1:SAMPLES
        R = PIN_MODE == "real" ? real_pins(u.map_parent_id) : random_pins(u, rand(RNG[], 1:3))
        (isempty(R) || R in Rs) || push!(Rs, R)
    end
    top = Int(u.current_step) - 1
    for R in Rs
        ram_ok() || (bump(:ram); return)
        U = pin(u, R)
        U.is_valid || continue
        bump(:runs)
        consec(U)
        PA, PB = pin(a, R), pin(b, R)
        for t in alive_at(U, top)
            bump(:tops)
            PG.is_alive(a.og, t) ? judge_top(U, t, a, PA) : judge_top(U, t, b, PB)
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :runs, :tops, :p_invalid, :fam_nodes, :fam_edges, :m1_node, :m1_tedge, :m1_edge, :m1_trio,
            :m2_cells, :m2_nowit, :m2_fail, :m2_fail_len, :m3_wit, :m3_dead, :m3_missing, :m3_deadS, :consec_fail, :ram)
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
