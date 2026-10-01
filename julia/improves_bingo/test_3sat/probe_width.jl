# Anchura del estado final como red de restricciones (1-oct-2026, rama reader-stuck; tras el v220).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_width.jl <salida.tsv>
#
# Con FORBID = :on (WIDTH_FORBID=off: control sin tríos). Sobre cada estado final revisado (reviewAll, el arranque del
# lector): cada paso es una variable, sus vivos son los valores, las aristas la relación binaria entre dos pasos y los
# tríos prohibidos la ternaria. Un par de pasos (s, l) es REAL si la relación no es «todo con todo» (algún vivo de s
# no es vecino de algún vivo de l); con tríos, además, si algún trío prohibido entre vivos vecinos toca los dos pasos.
# Teorema de Freuder (1982): si en el orden de lectura cada paso tiene a lo sumo w pares reales con pasos ya elegidos
# y el estado es fuertemente (w+1)-consistente, la lectura no retrocede.
#   steps, nodes      pasos y vivos del estado
#   one               pasos con un solo vivo (decididos)
#   real, real3       pares reales por aristas; pares añadidos solo por tríos
#   w_down, w_up      anchura por aristas en el orden cima → 0 (lector por caminos) y 0 → cima (lector por colores)
#   degen             mínima anchura sobre cualquier orden (degeneración del grafo de pares reales)
#   w_down3, w_up3, degen3   lo mismo con los pares de los tríos
#   span              mayor distancia |s − l| de un par real por aristas
#   tight             estrechez m (van Beek–Dechter 1997: relaciones m-estrechas + consistencia fuerte (m+2) ⟹
#                     consistencia global): el mayor número de vecinos en otro paso de un vivo que no los tiene todos
#   inc, inc_le2      incidencias (vivo, otro paso) sin todos los vecinos; las que tienen a lo sumo dos
#   exh               soluciones del exhaustivo
#   sols, dead        camarillas del estado (un vivo por paso, vecinos dos a dos, sin trío prohibido), contadas por
#                     DFS de la cima hacia abajo con TODOS los candidatos de cada paso; dead = callejones (cadena
#                     parcial sin candidato). Tope WIDTH_CAP hojas (sols = tope ⟹ cuenta cortada)
#   m1 … m6           cuenta SIN enumerar, por programación dinámica con memoria d: secuencias de un vivo por paso en
#                     las que cada ventana de d+1 pasos consecutivos es camarilla (sin trío prohibido). Si md = sols,
#                     el grafo tiene «memoria d»: lo que pasa a más de d pasos queda implicado por lo cercano
# Con varios estados finales, el máximo de cada columna (steps y nodes del primero).

const OUT = abspath(ARGS[1])
const MODE = Symbol(get(ENV, "WIDTH_FORBID", "on"))
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph

function reviewed(g)
    h = deepcopy(g)
    h.review_owners = true
    h.is_valid && GraphPath.filter!(h, SetNodesId())
    return h
end

# Anchura de un orden: máximo número de vecinos anteriores.
width(adj, order) = begin
    seen = Set{Int}(); w = 0
    for s in order
        w = max(w, count(in(seen), adj[s]))
        push!(seen, s)
    end
    w
end

# Degeneración: quitar siempre el de menor grado; el mayor grado visto al quitar.
function degeneracy(adj)
    deg = Dict(s => length(n) for (s, n) in adj)
    left = Set(keys(adj)); d = 0
    while !isempty(left)
        s = argmin(x -> deg[x], left)
        d = max(d, deg[s])
        delete!(left, s)
        for l in adj[s]
            l in left && (deg[l] -= 1)
        end
    end
    d
end

const CAP = parse(Int, get(ENV, "WIDTH_CAP", "200000"))

function count_cliques(og, alive, top)
    sols = Ref(0); deads = Ref(0); chain = PathNodeId[]
    ok(p) = all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        sols[] >= CAP && return
        push!(chain, x)
        if s == 0
            sols[] += 1
        else
            cs = [p for p in alive[s - 1] if ok(p)]
            isempty(cs) ? (deads[] += 1) : foreach(p -> dfs(p, s - 1), cs)
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, top), alive[top])
    return sols[], deads[]
end

function count_window(og, alive, top, d)
    fits(w, p) = all(x -> PG.has_edge(og, x, p), w) &&
                 !any(PG.dead_trio(og, w[i], w[j], p) for i in eachindex(w) for j in (i + 1):length(w))
    cur = Dict{Vector{PathNodeId}, BigInt}([t] => big(1) for t in alive[top])
    for s in (top - 1):-1:0
        nxt = Dict{Vector{PathNodeId}, BigInt}()
        for (w, n) in cur, p in alive[s]
            fits(w, p) || continue
            k = length(w) < d ? vcat(w, p) : vcat(w[2:end], p)
            nxt[k] = get(nxt, k, big(0)) + n
        end
        cur = nxt
    end
    return sum(values(cur); init = big(0))
end

function measure(g)
    og = g.og
    top = Int(g.current_step) - 1
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    adj = Dict(s => Set{Int}() for s in 0:top)
    real = 0; span = 0
    for s in 0:top, l in (s + 1):top
        if any(!PG.has_edge(og, x, w) for x in alive[s] for w in alive[l])
            push!(adj[s], l); push!(adj[l], s); real += 1; span = max(span, l - s)
        end
    end
    tight = 0; inc = 0; inc_le2 = 0
    for s in 0:top, l in 0:top
        s == l && continue
        for x in alive[s]
            n = count(w -> PG.has_edge(og, x, w), alive[l])
            n == length(alive[l]) && continue
            tight = max(tight, n); inc += 1; n <= 2 && (inc_le2 += 1)
        end
    end
    sols, deads = count_cliques(og, alive, top)
    ms = [count_window(og, alive, top, d) for d in 1:6]
    adj3 = Dict(s => copy(n) for (s, n) in adj)
    real3 = 0
    link(a, b) = (a == b || b in adj3[a]) ? 0 : (push!(adj3[a], b); push!(adj3[b], a); 1)
    for e in values(og.edges)
        isempty(e.forbid) && continue
        (PG.is_alive(og, e.a) && PG.is_alive(og, e.b)) || continue
        sa = Int(e.a.id.step); sb = Int(e.b.id.step)
        for r in e.forbid
            (PG.is_alive(og, r) && PG.has_edge(og, e.a, r) && PG.has_edge(og, e.b, r)) || continue
            sr = Int(r.id.step)
            real3 += link(sa, sb) + link(sa, sr) + link(sb, sr)
        end
    end
    down = top:-1:0; up = 0:top
    return (steps = top + 1, nodes = sum(length, values(alive)), one = count(s -> length(alive[s]) == 1, 0:top),
            real = real, real3 = real3, w_down = width(adj, down), w_up = width(adj, up), degen = degeneracy(adj),
            w_down3 = width(adj3, down), w_up3 = width(adj3, up), degen3 = degeneracy(adj3), span = span,
            tight = tight, inc = inc, inc_le2 = inc_le2, sols = sols, dead = deads,
            m1 = ms[1], m2 = ms[2], m3 = ms[3], m4 = ms[4], m5 = ms[5], m6 = ms[6])
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:steps, :nodes, :one, :real, :real3, :w_down, :w_up, :degen, :w_down3, :w_up3, :degen3, :span, :tight, :inc, :inc_le2, :sols, :dead, :m1, :m2, :m3, :m4, :m5, :m6)
    header = "instance\ttruth\texh\tfinals\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        nex = ex === nothing ? "?" : length(ex)
        PG.FORBID[] = MODE
        machine = SatMachine.new(loader(path))
        rows = []
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            if SatMachine.have_solution(machine)
                for g in SatMachine.get_gpath_solutions(machine)
                    h = reviewed(g)
                    h.is_valid && push!(rows, measure(h))
                end
            end
        end
        PG.FORBID[] = :off
        isempty(rows) && return (truth, nex, 0, ("-" for _ in cols)..., round(t, digits = 1))
        val(c) = c in (:steps, :nodes, :inc, :inc_le2, :sols, :dead, :m1, :m2, :m3, :m4, :m5, :m6) ? getfield(rows[1], c) : maximum(getfield(r, c) for r in rows)
        return (truth, nex, length(rows), (val(c) for c in cols)..., round(t, digits = 1))
    end
end

main()
