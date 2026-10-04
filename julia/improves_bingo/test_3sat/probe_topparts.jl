# Las piezas de TopSideAt (1-oct-2026, rama reader-stuck; lean ForbidOnParts.lean).
#
#   PIN_MODE=random|real PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_topparts.jl <salida.tsv> [muestras]
#
# Con FORBID = :on. En cada join, para R = [] y pins R (como probe_pinside.jl): U = pin(join(A,B), R). Para cada cima
# viva t de U, con b = el color de su padre (t.parent_id) y S el lado donde t está viva:
#   tops        — cimas vivas de U
#   keep_fail   — TopKeepAt: U' = pin(join(A,B), R ∪ {b}) no es válido o no tiene a t
# y para cada U' válido (uno por color b):
#   pins        — uniones fijadas en el color de un lado
#   top_other   — cimas de U' que no son del lado S (demostrado: 0)
#   node_out    — vivos de U' que no están vivos en S (demostrado: 0)
#   edge_out    — aristas de U' que no son de S (demostrado: 0)
#   tris        — triángulos de U'
#   tri_fail    — TriSideAt: triángulos de U' prohibidos en S (sin fijar) y no en U'
#   tri_fail_p  — lo mismo contra S fijado en R ∪ {b} (control: ¿y tras el review de S?)
# y para cada lado S de cada join (sin pins), TopFace: ¿puede un triángulo prohibido en S tener una cima de S vecina de
# los tres con sus tres caras sin prohibir?
#   dead_tri    — triángulos prohibidos en S (con sus tres aristas)
#   face_fail   — los que tienen una cima así
#   face_low    — de esos, los que no tocan los dos pasos de arriba (cima y remitente), que el join no corta solo

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 3
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
allalive(g) = [x for (_, xs) in g.og.alive for x in xs]

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

function judge_side(U2, S, SP)
    bump(:pins)
    top = Int(U2.current_step) - 1
    for t in alive_at(U2, top)
        PG.is_alive(S.og, t) || bump(:top_other)
    end
    for x in allalive(U2)
        PG.is_alive(S.og, x) || bump(:node_out)
    end
    for (k, e) in U2.og.edges
        PG.has_edge(S.og, e.a, e.b) || bump(:edge_out)
    end
    for (k, e) in U2.og.edges, r in collect(PG.neighbors_all(U2.og, e.a))
        (r == e.a || r == e.b || !PG.has_edge(U2.og, e.b, r)) && continue
        PG.node_ord(e.b) < PG.node_ord(r) || continue
        bump(:tris)
        PG.dead_trio(U2.og, e.a, e.b, r) && continue
        if PG.has_edge(S.og, e.a, e.b) && PG.has_edge(S.og, e.a, r) && PG.has_edge(S.og, e.b, r) &&
           PG.dead_trio(S.og, e.a, e.b, r)
            bump(:tri_fail)
        end
        if SP.is_valid && PG.has_edge(SP.og, e.a, e.b) && PG.has_edge(SP.og, e.a, r) && PG.has_edge(SP.og, e.b, r) &&
           PG.dead_trio(SP.og, e.a, e.b, r)
            bump(:tri_fail_p)
        end
    end
end

function topface(S)
    top = Int(S.current_step) - 1
    tops = alive_at(S, top)
    for (k, e) in S.og.edges, r in collect(e.forbid)
        (PG.has_edge(S.og, e.a, r) && PG.has_edge(S.og, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        bump(:dead_tri)
        tri = (e.a, e.b, r)
        any(x -> Int(x.id.step) == top, tri) && continue
        for t in tops
            all(x -> PG.has_edge(S.og, t, x), tri) || continue
            (PG.dead_trio(S.og, t, e.a, e.b) || PG.dead_trio(S.og, t, e.a, r) || PG.dead_trio(S.og, t, e.b, r)) && continue
            bump(:face_fail)
            all(x -> Int(x.id.step) <= top - 2, tri) && bump(:face_low)
            break
        end
    end
end

function judge(u, a, b)
    u.is_valid || return
    bump(:joins)
    topface(a); topface(b)
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
        done = Dict{Any, Any}()
        for t in alive_at(U, top)
            bump(:tops)
            c = t.parent_id
            c === nothing && continue
            S = PG.is_alive(a.og, t) ? a : b
            if !haskey(done, c)
                U2 = pin(u, vcat(R, [c]))
                done[c] = U2
                U2.is_valid && judge_side(U2, S, pin(S, vcat(R, [c])))
            end
            U2 = done[c]
            (U2.is_valid && PG.is_alive(U2.og, t)) || bump(:keep_fail)
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :runs, :tops, :keep_fail, :pins, :top_other, :node_out, :edge_out, :tris, :tri_fail, :tri_fail_p, :dead_tri, :face_fail, :face_low, :ram)
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
