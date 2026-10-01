# Las bases muertas en un lado y vivas en la unión fijada: ¿sobrevive la cima?, ¿sigue cerrada su estrella?
# (1-oct-2026, rama reader-stuck; tras refutarse CrossCut en v7, probe_prevbig.jl)
#
#   PIN_MODE=real PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_topdead.jl <salida.tsv> [muestras]
#
# Con FORBID = :on. En cada join, para R = [] y pins R: U = pin(join(A,B), R). Para cada cima viva t de U, con S el
# lado donde t está viva y P = pin(S, R):
#
# TopSideAt (lo que el veredicto necesita): tops, top_dead (P no es válido o t no está viva en P).
# Bases bajo t en U (triángulos entre vecinos de t, con sus tres caras con t sin prohibir en U):
#   bases, b_deadU (prohibida en U), rev (viva en U y prohibida en S: la base «revive» en la unión; CrossCut la
#   excluía), revP (viva en U y prohibida en P: lo que StarTriAt excluye), rev_tops (cimas con alguna rev).
# La hipótesis reformulada, solo en las cimas con alguna rev: la familia de t en U (t y sus vecinos; parejas con el
#   trío con t sin prohibir) con los tríos T' = (prohibidos en U) ∪ (triángulos de la familia prohibidos en S):
#   e_cells / e_fail   aristas de la familia × paso: sin testigo (nodo de la familia vecino de los dos, con el trío
#                      fuera de T')            e_failT: tampoco con T = prohibidos en U (el punto fijo dice 0)
#   tt_cells / tt_fail triángulos con t fuera de T' × paso: sin testigo bueno (vecino de los tres, sus tres caras
#                      nuevas fuera de T')     tt_failT: tampoco con T
#   tb_cells / tb_fail lo mismo para las bases (triángulos sin t) fuera de T';   tb_failT: con T (es Star4At)

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
const GMAP = Ref{Any}(nothing)

ram_ok() = Sys.maxrss() / 2^20 < RAM_MB
alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
edge(g, a, b) = PG.has_edge(g.og, a, b)
dead(g, a, b, r) = PG.has_edge(g.og, a, b) && PG.dead_trio(g.og, a, b, r)
tridead(g, a, b, r) = edge(g, a, b) && edge(g, a, r) && edge(g, b, r) && PG.dead_trio(g.og, a, b, r)
st(x) = Int(x.id.step)

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

# la familia de t en U, cerrada o no con los tríos T' (y con T)
function closure(U, t, S, N)
    F = [t; N]
    rr(y, w) = y == w || ((y == t || w == t) ? edge(U, y, w) : (edge(U, y, w) && !dead(U, t, y, w)))
    inT(a, b, c) = PG.dead_trio(U.og, a, b, c)
    inT2(a, b, c) = inT(a, b, c) || tridead(S, a, b, c)
    bystep = Dict{Int, Vector{PathNodeId}}()
    for y in F
        push!(get!(bystep, st(y), PathNodeId[]), y)
    end
    top = st(t)
    for i in eachindex(F), j in i+1:length(F)
        y, w = F[i], F[j]
        rr(y, w) || continue
        for l in 0:top
            cand = [s for s in get(bystep, l, PathNodeId[]) if rr(y, s) && rr(w, s)]
            bump(:e_cells)
            any(s -> s == y || s == w || !inT2(y, w, s), cand) || bump(:e_fail)
            any(s -> s == y || s == w || !inT(y, w, s), cand) || bump(:e_failT)
        end
        for k in j+1:length(F)
            r = F[k]
            (rr(y, r) && rr(w, r)) || continue
            hast = i == 1
            inU = inT(y, w, r)
            in2 = inU || tridead(S, y, w, r)
            for l in 0:top
                cand = [s for s in get(bystep, l, PathNodeId[]) if rr(y, s) && rr(w, s) && rr(r, s)]
                if !in2
                    bump(hast ? :tt_cells : :tb_cells)
                    any(s -> s == y || s == w || s == r || (!inT2(y, w, s) && !inT2(y, r, s) && !inT2(w, r, s)), cand) ||
                        bump(hast ? :tt_fail : :tb_fail)
                end
                if !inU
                    any(s -> s == y || s == w || s == r || (!inT(y, w, s) && !inT(y, r, s) && !inT(w, r, s)), cand) ||
                        bump(hast ? :tt_failT : :tb_failT)
                end
            end
        end
    end
end

function judge_top(U, t, S, P)
    pv = P.is_valid
    (pv && PG.is_alive(P.og, t)) || bump(:top_dead)
    N = [y for y in collect(PG.neighbors_all(U.og, t)) if y != t && PG.is_alive(U.og, y)]
    nrev = 0
    for i in eachindex(N), j in i+1:length(N)
        x, y = N[i], N[j]
        (edge(U, x, y) && !dead(U, t, x, y)) || continue
        for k in j+1:length(N)
            z = N[k]
            (edge(U, x, z) && edge(U, y, z) && !dead(U, t, x, z) && !dead(U, t, y, z)) || continue
            bump(:bases)
            if PG.dead_trio(U.og, x, y, z)
                bump(:b_deadU)
            else
                if tridead(S, x, y, z)
                    bump(:rev); nrev += 1
                end
                (pv && tridead(P, x, y, z)) && bump(:revP)
            end
        end
    end
    if nrev > 0
        bump(:rev_tops)
        closure(U, t, S, N)
    end
end

function judge(u, a, b)
    u.is_valid || return
    bump(:joins)
    Rs = Any[NodeId[]]
    for _ in 1:SAMPLES
        R = real_pins(u.map_parent_id)
        (isempty(R) || R in Rs) || push!(Rs, R)
    end
    top = Int(u.current_step) - 1
    for R in Rs
        ram_ok() || (bump(:ram); return)
        U = pin(u, R)
        U.is_valid || continue
        bump(:runs)
        PA, PB = pin(a, R), pin(b, R)
        for t in alive_at(U, top)
            bump(:tops)
            PG.is_alive(a.og, t) ? judge_top(U, t, a, PA) : judge_top(U, t, b, PB)
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :runs, :tops, :top_dead, :bases, :b_deadU, :rev, :revP, :rev_tops, :e_cells, :e_fail, :e_failT,
            :tt_cells, :tt_fail, :tt_failT, :tb_cells, :tb_fail, :tb_failT, :ram)
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
