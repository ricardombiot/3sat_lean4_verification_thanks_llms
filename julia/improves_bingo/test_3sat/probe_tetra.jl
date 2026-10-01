# Los tetraedros con cima: qué los mata en la unión, y si la estrella cierra a nivel cuatro
# (1-oct-2026, rama reader-stuck; lean ForbidOnStar.lean, StarTriAt).
#
#   PIN_MODE=random|real PROBE_MAP=bin PROBE_ONLY=... julia --project=. test_3sat/probe_tetra.jl <salida.tsv> [muestras]
#
# Con FORBID = :on. En cada join, con los lados A y B y la unión sin revisar u:
#
# SONDA 1 — para cada tetraedro «TopFace» de un lado S (cima t de S, base (x, y, z) prohibida en S con sus tres
# aristas, t vecina de los tres y las caras (t,x,y), (t,x,z), (t,y,z) sin prohibir en S), y para R = [] y pins R, en
# U = pin(u, R), el primer motivo por el que no es un tetraedro vivo de U:
#   tf            — tetraedros TopFace × pins
#   tf_low        — de ellos, con la base entera dos pasos o más por debajo de la cima (el join no la corta solo)
#   k_invalid     — U no es válido
#   k_top         — la cima no está viva en U
#   k_node        — un nodo de la base no está vivo en U
#   k_tedge       — falta una arista de la cima a la base
#   k_bedge       — falta una arista de la base
#   k_base_join   — la base está prohibida ya en u (la guardó el join: el otro lado también la corta)
#        de esos: o_node (al otro lado le falta un nodo), o_edge (le falta una arista), o_dead (la tiene prohibida)
#   k_base_rule   — la base la prohíbe la regla en el review de U
#   k_face_join   — una cara con la cima prohibida ya en u
#   k_face_rule   — una cara con la cima prohibida por la regla en U
#   k_alive       — sigue vivo entero (violaría StarTriAt en su mitad «sin fijar»: se espera 0)
#   (las columnas *_low son lo mismo, solo para tf_low)
# y, sin pins ni review, una vez por join (CrossCut): ¿el otro lado corta también la base?
#   x_tetra, x_cut (le falta un nodo, una arista, o la tiene prohibida), x_open (la tiene como triángulo sin prohibir);
#   x_tetra_low, x_open_low
#
# SONDA 2 — la estrella a nivel cuatro: para cada cima viva t de U y una muestra de tetraedros vivos (t, a, b, r)
# (vecinos de t, las cuatro caras sin prohibir en U), y cada paso l por debajo de la cima que no sea el de a, b, r:
# ¿hay un vecino s de t en el paso l, vecino de a, b, r, con las seis caras nuevas sin prohibir en U?
#   q_tetra, q_cells, q_fail (ningún s), q_fail_tetra (tetraedros con algún paso sin s)

using Random
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 2
const RAM_MB = parse(Int, get(ENV, "PROBE_RAM_MB", "3500"))
const TRI_CAP = parse(Int, get(ENV, "TRI_CAP", "150"))
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

# los tetraedros TopFace de un lado: (t, x, y, z)
function topface(S)
    top = Int(S.current_step) - 1
    tops = alive_at(S, top)
    out = NTuple{4, PathNodeId}[]
    for (k, e) in S.og.edges, r in collect(e.forbid)
        (edge(S, e.a, r) && edge(S, e.b, r)) || continue
        (PG.node_ord(e.b) < PG.node_ord(r)) || continue
        any(x -> st(x) == top, (e.a, e.b, r)) && continue
        for t in tops
            all(x -> edge(S, t, x), (e.a, e.b, r)) || continue
            (PG.dead_trio(S.og, t, e.a, e.b) || PG.dead_trio(S.og, t, e.a, r) || PG.dead_trio(S.og, t, e.b, r)) && continue
            push!(out, (t, e.a, e.b, r))
        end
    end
    return out
end

function classify(u, U, O, q)
    t, x, y, z = q
    U.is_valid || return :k_invalid
    PG.is_alive(U.og, t) || return :k_top
    all(n -> PG.is_alive(U.og, n), (x, y, z)) || return :k_node
    all(n -> edge(U, t, n), (x, y, z)) || return :k_tedge
    (edge(U, x, y) && edge(U, x, z) && edge(U, y, z)) || return :k_bedge
    if PG.dead_trio(U.og, x, y, z)
        if dead(u, x, y, z)
            if !all(n -> PG.is_alive(O.og, n), (x, y, z))
                bump(:o_node)
            elseif !(edge(O, x, y) && edge(O, x, z) && edge(O, y, z))
                bump(:o_edge)
            else
                bump(:o_dead)
            end
            return :k_base_join
        end
        return :k_base_rule
    end
    for (p, q2) in ((x, y), (x, z), (y, z))
        if PG.dead_trio(U.og, t, p, q2)
            return dead(u, t, p, q2) ? :k_face_join : :k_face_rule
        end
    end
    return :k_alive
end

function star4(U)
    top = Int(U.current_step) - 1
    for t in alive_at(U, top)
        N = [y for y in collect(PG.neighbors_all(U.og, t)) if y != t && PG.is_alive(U.og, y)]
        bystep = Dict{Int, Vector{PathNodeId}}()
        foreach(y -> push!(get!(bystep, st(y), PathNodeId[]), y), N)
        tetra = NTuple{3, PathNodeId}[]
        n = length(N)
        tries = 0
        while length(tetra) < TRI_CAP && tries < 40 * TRI_CAP && n >= 3
            tries += 1
            a, b, r = N[rand(RNG[], 1:n)], N[rand(RNG[], 1:n)], N[rand(RNG[], 1:n)]
            (a != b && a != r && b != r) || continue
            (edge(U, a, b) && edge(U, a, r) && edge(U, b, r)) || continue
            (PG.dead_trio(U.og, a, b, r) || PG.dead_trio(U.og, t, a, b) || PG.dead_trio(U.og, t, a, r) ||
             PG.dead_trio(U.og, t, b, r)) && continue
            push!(tetra, (a, b, r))
        end
        for (a, b, r) in tetra
            bump(:q_tetra)
            bad = false
            for l in 0:top-1
                (l == st(a) || l == st(b) || l == st(r)) && continue
                bump(:q_cells)
                ok = false
                for s in get(bystep, l, PathNodeId[])
                    (edge(U, a, s) && edge(U, b, s) && edge(U, r, s)) || continue
                    (PG.dead_trio(U.og, t, a, s) || PG.dead_trio(U.og, t, b, s) || PG.dead_trio(U.og, t, r, s) ||
                     PG.dead_trio(U.og, a, b, s) || PG.dead_trio(U.og, a, r, s) || PG.dead_trio(U.og, b, r, s)) && continue
                    ok = true; break
                end
                ok || (bump(:q_fail); bad = true)
            end
            bad && bump(:q_fail_tetra)
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
    tfa, tfb = topface(a), topface(b)
    for (tf, O) in ((tfa, b), (tfb, a)), q in tf
        x, y, z = q[2], q[3], q[4]
        low = all(n -> st(n) <= top - 2, (x, y, z))
        bump(:x_tetra); low && bump(:x_tetra_low)
        if edge(O, x, y) && edge(O, x, z) && edge(O, y, z) && !PG.dead_trio(O.og, x, y, z)
            bump(:x_open); low && bump(:x_open_low)
        else
            bump(:x_cut)
        end
    end
    for R in Rs
        ram_ok() || (bump(:ram); return)
        U = pin(u, R)
        for (tf, O) in ((tfa, b), (tfb, a)), q in tf
            bump(:tf)
            low = all(n -> st(n) <= top - 2, q[2:4])
            low && bump(:tf_low)
            k = classify(u, U, O, q)
            bump(k)
            low && bump(Symbol(string(k), "_low"))
        end
        U.is_valid && star4(U)
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    ks = (:k_invalid, :k_top, :k_node, :k_tedge, :k_bedge, :k_base_join, :k_base_rule, :k_face_join, :k_face_rule, :k_alive)
    cols = (:joins, :x_tetra, :x_cut, :x_open, :x_tetra_low, :x_open_low, :tf, ks..., :o_node, :o_edge, :o_dead, :tf_low, (Symbol(string(k), "_low") for k in ks)...,
            :q_tetra, :q_cells, :q_fail, :q_fail_tetra, :ram)
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
