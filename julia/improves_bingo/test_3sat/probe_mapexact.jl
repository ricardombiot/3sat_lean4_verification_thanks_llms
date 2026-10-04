# MapExact frente a EdgeClique (29-sept-2026, rama reader-stuck; Lean `PinKeeps.lean`).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_mapexact.jl <salida.tsv> [tope_cadenas]
#   (con tope de memoria: test_3sat/run_capped.sh <MB> <s> julia …)
#
# En Lean, la completitud del lector se reduce a `PinKeeps` ⇔ `MapExact` (ReaderStuck.lean, PinKeeps.lean):
#   MapExact g: si g lleva una camarilla, todo nodo de mapa b de un paso con elección cuyo pin (filter! con review)
#   deja g válido tiene alguna camarilla por b — es decir, pin(g, b) no es un zombi.
# Es la exactitud del review en su versión de existencia y de un solo pin. EdgeClique (toda arista y nodo vivo en una
# camarilla) es la versión por parejas. La pregunta: ¿la existencia es más débil de verdad (vale donde EdgeClique
# falla)? ¿y se conserva en el join sin las parejas?
#
# Puntos (puntos de sonda de src, src/utils/probes.jl):
#   U  — tras el UP con su review (:up_done)
#   J  — tras el join, sin review (:join_post); con los dos lados copiados en :join_pre
#   L  — los gpath de la línea final, revisados enteros (el arranque del lector en Lean, reviewAll)
#   R  — los estados que visita el lector sin retroceso (Lean `readLoop`) desde cada estado de L
# Por punto: n (estados válidos juzgados), zomb (válidos sin camarilla), ec_fail, ec_trunc, me_fail (estados con
# algún pin válido y zombi), pins (pins válidos probados), pins_bad, me_ok_ec_fail (MapExact sí, EdgeClique no).
# Join: j_sides_me (joins con los dos lados MapExact), j_break (de esos, unión sin MapExact).
# Lector: r_start (arranques válidos), r_stuck (atascados), truth.

const OUT = abspath(ARGS[1])
const CAP = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const PCL = PathCollectionLines

# ---------- camarillas ----------

"¿Hay alguna camarilla llevada (cadena de enlaces raíz → cima, viva, poseída dos a dos)? nothing si se pasa del tope."
function has_clique(g :: GPath; cap :: Int = CAP) :: Union{Nothing, Bool}
    og = g.og
    top = g.current_step - 1
    top < 0 && return true
    chain = PathNodeId[]
    visits = Ref(0)
    function ext(x)
        visits[] += 1
        visits[] > cap && return nothing
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

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in og.alive[k]), by = n -> n.index)
pin(g, reqs) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(reqs)); g2)
reviewed(g) = (g2 = deepcopy(g); g2.review_owners = true; GraphPath.filter!(g2, SetNodesId()); g2)

# ---------- medidas ----------

const PTS = (:U, :J, :L, :R)
const COLS = (:n, :zomb, :ec_fail, :ec_trunc, :me_fail, :pins, :pins_bad, :me_ok_ec_fail)
const ACC = Dict{Symbol, Dict{Symbol, Int}}()
reset_acc!() = for p in PTS; ACC[p] = Dict(c => 0 for c in COLS); end
bump(p, c, n = 1) = (ACC[p][c] += n)

"(ok, pins, bad) de MapExact en g; ok = nothing si algún juicio se pasó del tope."
function map_exact(g :: GPath)
    pins = 0; bad = 0; unknown = false
    for k in choice_steps(g.og), b in map_nodes(g.og, k)
        h = pin(g, [b])
        h.is_valid || continue
        pins += 1
        c = has_clique(h)
        c === nothing && (unknown = true; continue)
        c || (bad += 1)
    end
    return (bad > 0 ? false : (unknown ? nothing : true)), pins, bad
end

"Mide g en el punto p; devuelve si cumple MapExact (true / false / nothing)."
function look!(p :: Symbol, g :: GPath)
    g.is_valid || return nothing
    bump(p, :n)
    hc = has_clique(g)
    hc === false && bump(p, :zomb)
    ec = GraphPath.edge_clique_miss(g; cap = CAP)
    ec === nothing && bump(p, :ec_trunc)
    ec_ok = ec === nothing ? nothing : ec == (0, 0)
    ec_ok === false && bump(p, :ec_fail)
    # MapExact solo pide algo a los estados con camarilla
    hc === true || return (hc === false ? true : nothing)
    me, pins, bad = map_exact(g)
    bump(p, :pins, pins); bump(p, :pins_bad, bad)
    me === false && bump(p, :me_fail)
    me === true && ec_ok === false && bump(p, :me_ok_ec_fail)
    return me
end

const JOIN = Dict{Symbol, Int}(:j_sides_me => 0, :j_break => 0)
const PENDING = Ref{Any}(nothing)

function on_join_pre(a, b)
    ma = look_quiet(a); mb = look_quiet(b)
    PENDING[] = (ma === true && mb === true)
end
look_quiet(g) = (hc = has_clique(g); hc === true ? map_exact(g)[1] : (hc === false ? true : nothing))

function on_join_post(g)
    m = look!(:J, g)
    if PENDING[] === true
        JOIN[:j_sides_me] += 1
        m === false && (JOIN[:j_break] += 1)
    end
    PENDING[] = nothing
end

# ---------- el lector sin retroceso (Lean readLoop) ----------

"Recorre el lector desde g (ya revisado); mide cada estado visitado en R. Devuelve :done o :stuck."
function read_no_backtrack!(g :: GPath)
    h = g
    while true
        look!(:R, h)
        steps = choice_steps(h.og)
        isempty(steps) && return :done
        k = first(steps)
        next = nothing
        for b in map_nodes(h.og, k)
            h2 = pin(h, [b])
            h2.is_valid && (next = h2; break)
        end
        next === nothing && return :stuck
        h = next
    end
end

# ---------- arnés ----------

function run_one(path, loader)
    reset_acc!(); JOIN[:j_sides_me] = 0; JOIN[:j_break] = 0
    machine = SatMachine.new(loader(path))
    Probes.with(:up_done => g -> look!(:U, g), :join_pre => on_join_pre, :join_post => on_join_post) do
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
    end
    r_start = 0; r_stuck = 0
    for g in SatMachine.get_gpath_list(machine)
        g.is_valid || continue
        g0 = reviewed(g)
        look!(:L, g0)
        g0.is_valid || continue
        r_start += 1
        read_no_backtrack!(g0) == :stuck && (r_stuck += 1)
    end
    return r_start, r_stuck
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    header = "instance\ttruth\t" * join(["$(p)_$(c)" for p in PTS for c in COLS], "\t") *
             "\tj_sides_me\tj_break\tr_start\tr_stuck"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf"])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        r_start, r_stuck = run_one(path, loader)
        return (truth, (ACC[p][c] for p in PTS for c in COLS)..., JOIN[:j_sides_me], JOIN[:j_break], r_start, r_stuck)
    end
end

main()
