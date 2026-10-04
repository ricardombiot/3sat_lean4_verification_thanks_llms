# SecExactIn y SecSplitIn (29-sept-2026, rama reader-stuck; Lean `AvoidSplit.lean`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_secin.jl <salida.tsv> [muestras] [semilla]
#
# SecExactIn g: toda estructura cerrada no vacía de g contiene una camarilla (no solo que exista una fuera).
# SecSplitIn e g: toda estructura cerrada no vacía de la unión contiene una estructura cerrada no vacía de un lado.
# Estructuras cerradas al azar: se restringe el estado a un subconjunto al azar U de sus vivos (cada vivo se queda con
# probabilidad p ∈ {0.5, 0.7, 0.9}) y se revisa; lo que queda es la mayor estructura cerrada dentro de U.
#   U (tras el UP, :up_done): si la restricción es válida, ¿tiene camarilla? in_t / in_f
#   S2 (en el join): SplitIn2 — dentro de V, fijar el color de e o el de g deja algo: s2_t / s2_f / s2_both
#   (ii) mixed_v: V con los dos colores en k; pres_t / pres_f: colores presentes en V que (no) sobreviven al fijarlos
#   nc_t / nc_f: NodeCliqueIn — vivos de la estructura (tras el UP y en la unión) que (no) están en una camarilla dentro
#   de ella
#   ncol_t / ncol_f: NodeColour — vivos de V que (no) sobreviven a fijar dentro de V el color de algún lado
#   node_t / node_f: nodos de V en k que (no) siguen vivos al fijar su propio color dentro de V
#   J (en el join): si la restricción de la unión V es válida, ¿la de e o la de g a los vivos de V es válida?
#     sp_t / sp_f; y SecExactIn en V: jin_t / jin_f
# Por instancia: in_t, in_f, sp_t, sp_f, jin_t, jin_f, trunc (juicios de camarilla que se pasan del tope).

using Random

const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 4
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260929
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const PCL = PathCollectionLines
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const RNG = Ref(MersenneTwister(SEED))

alive(h) = [x for (_, xs) in h.og.alive for x in xs]

"La mayor estructura cerrada de g dentro de U: se quitan los vivos fuera de U y se revisa."
function restrict(g, U :: Set{PathNodeId})
    h = deepcopy(g)
    for x in alive(h)
        x in U && continue
        GraphPath.remove_node_owner!(h, x; rule = :probe)
    end
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

"¿Hay alguna camarilla llevada? nothing si se pasa del tope."
function has_clique(g) :: Union{Nothing, Bool}
    og = g.og; top = g.current_step - 1
    top < 0 && return true
    chain = PathNodeId[]; visits = Ref(0)
    function ext(x)
        visits[] += 1
        visits[] > CAP && return nothing
        push!(chain, x)
        found = false
        if x.id.step == top
            found = true
        else
            n = PCL.get_node(g.table_lines, x)
            if n !== nothing
                for s in n.sons
                    PG.is_alive(og, s) || continue
                    PCL.get_node(g.table_lines, s) === nothing && continue
                    all(a -> PG.has_edge(og, a, s), chain) || continue
                    r = ext(s)
                    r === nothing && (pop!(chain); return nothing)
                    r && (found = true; break)
                end
            end
        end
        pop!(chain)
        return found
    end
    for r in get(og.alive, 0, SetPathNodesId())
        r.parent_id === nothing || continue
        PCL.get_node(g.table_lines, r) === nothing && continue
        PG.has_edge(og, r, r) || continue
        res = ext(r)
        res === nothing && return nothing
        res && return true
    end
    return false
end

"¿Hay una camarilla de g que pase por x? nothing si se pasa del tope."
function on_clique(g, x) :: Union{Nothing, Bool}
    og = g.og; top = g.current_step - 1
    chain = PathNodeId[]; visits = Ref(0)
    function ext(y)
        visits[] += 1
        visits[] > CAP && return nothing
        (y.id.step == x.id.step && y != x) && return false
        push!(chain, y)
        found = false
        if y.id.step == top
            found = x in chain
        else
            n = PCL.get_node(g.table_lines, y)
            if n !== nothing
                for s in n.sons
                    PG.is_alive(og, s) || continue
                    PCL.get_node(g.table_lines, s) === nothing && continue
                    all(a -> PG.has_edge(og, a, s), chain) || continue
                    r = ext(s)
                    r === nothing && (pop!(chain); return nothing)
                    r && (found = true; break)
                end
            end
        end
        pop!(chain)
        return found
    end
    for r in get(og.alive, 0, SetPathNodesId())
        r.parent_id === nothing || continue
        PCL.get_node(g.table_lines, r) === nothing && continue
        PG.has_edge(og, r, r) || continue
        res = ext(r)
        res === nothing && return nothing
        res && return true
    end
    return false
end

subset(g) = (p = rand(RNG[], (0.5, 0.7, 0.9)); Set(x for x in alive(g) if rand(RNG[]) < p))

function judge_in!(h, t, f)
    h.is_valid || return
    c = has_clique(h)
    c === nothing && (bump(:trunc); return)
    bump(t); c || bump(f)
    # NodeCliqueIn: todo vivo de la estructura está en una camarilla dentro de ella
    for (_, xs) in h.og.alive, x in xs
        o = on_clique(h, x)
        o === nothing && (bump(:trunc); continue)
        bump(:nc_t); o || bump(:nc_f)
    end
end

function on_up(g)
    g.is_valid || return
    for _ in 1:SAMPLES
        judge_in!(restrict(g, subset(g)), :in_t, :in_f)
    end
end

const SIDES = Ref{Any}(nothing)
function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    for _ in 1:SAMPLES
        V = restrict(u, subset(u))
        V.is_valid || continue
        judge_in!(V, :jin_t, :jin_f)
        W = Set(alive(V))
        bump(:sp_t)
        (restrict(e, W).is_valid || restrict(g, W).is_valid) || bump(:sp_f)
        # SplitIn2: dentro de V, fijar el color de un lado (paso del remitente) deja algo
        k = u.current_step - 2
        cols = unique(x.id for x in get(u.og.alive, k, SetPathNodesId()))
        if length(cols) == 2
            bump(:s2_t)
            pa = (h = deepcopy(V); GraphPath.filter!(h, SetNodesId([cols[1]])); h.is_valid)
            ps = (h = deepcopy(V); GraphPath.filter!(h, SetNodesId([cols[2]])); h.is_valid)
            (pa || ps) || bump(:s2_f)
            (pa && ps) && bump(:s2_both)
            # (ii) todo color presente en V en el paso k sobrevive al fijarlo dentro de V
            present = unique(x.id for x in get(V.og.alive, k, SetPathNodesId()))
            length(present) == 2 && bump(:mixed_v)
            for (c, ok) in ((cols[1], pa), (cols[2], ps))
                c in present || continue
                bump(:pres_t)
                ok || bump(:pres_f)
            end
            # NodeColour: todo vivo x de V sigue vivo al fijar dentro de V el color de algún lado
            Aa = pa ? (h = deepcopy(V); GraphPath.filter!(h, SetNodesId([cols[1]])); Set(x for (_, xs) in h.og.alive for x in xs)) : Set{PathNodeId}()
            As = ps ? (h = deepcopy(V); GraphPath.filter!(h, SetNodesId([cols[2]])); Set(x for (_, xs) in h.og.alive for x in xs)) : Set{PathNodeId}()
            for (_, xs) in V.og.alive, x in xs
                bump(:ncol_t)
                (x in Aa || x in As) || bump(:ncol_f)
            end
            # nodo a nodo: cada vivo x de V en k, ¿sigue vivo al fijar su color dentro de V?
            for c in present
                h = deepcopy(V); GraphPath.filter!(h, SetNodesId([c]))
                A = h.is_valid ? Set(x for (_, xs) in h.og.alive for x in xs) : Set{PathNodeId}()
                for x in get(V.og.alive, k, SetPathNodesId())
                    x.id == c || continue
                    bump(:node_t)
                    x in A || bump(:node_f)
                end
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:in_t, :in_f, :sp_t, :sp_f, :jin_t, :jin_f, :s2_t, :s2_f, :s2_both, :mixed_v, :pres_t, :pres_f, :node_t, :node_f, :nc_t, :nc_f, :ncol_t, :ncol_f, :trunc)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:up_done => on_up, :join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b))),
                                 :join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
