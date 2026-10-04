# Qué mata a las parejas de un solo lado al fijar la unión en un color (29-sept-2026, rama reader-stuck).
#
#   PROBE_MAP=bin julia --project=. test_3sat/dump_gonly.jl <cnf> [n_casos]
#
# En cada join de dos lados e (color a) y g (color s), se fija la unión en a. Las parejas «solo de g» son posesiones
# de la unión entre nodos compartidos que g tiene y e no. Se sigue la cascada del review de ese pin vuelta a vuelta
# (punto de sonda :review_round) y, para cada pareja solo-de-g, se cuenta en qué vuelta muere y por qué:
#   :node   — murió un extremo (la pareja se va con él)
#   :pair@l — en la vuelta anterior, los dos extremos ya no comparten testigo en el paso l (regla de parejas), y se dice
#             si l es el paso del remitente (k), la cima, o de qué lado venían los testigos que tenían en la unión.
# Vuelca el caso más pequeño con parejas solo-de-g, y un resumen de causas en todos.

const CNF = abspath(ARGS[1])
const NCASES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 1
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
key(x) = Alias.as_key(x)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
ekeys(h) = Set(keys(h.og.edges))

const SIDES = Ref{Any}(nothing)
const CASES = Any[]
const CAUSES = Dict{String, Int}()
const CUT = Dict{String, Int}()     # en el corte por la regla de parejas: pasos sin testigo común
const CUTN = Ref(0)

# testigos comunes de y, w en el paso l en el grafo og (vivos)
common(og, y, w, l) = [r for r in get(og.alive, l, SetPathNodesId()) if PG.has_edge(og, y, r) && PG.has_edge(og, w, r)]

function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    k = u.current_step - 2
    k >= 0 || return
    cols = unique(x.id for x in get(u.og.alive, k, SetPathNodesId()))
    length(cols) == 2 || return
    a = first(unique(x.id for x in get(e.og.alive, k, SetPathNodesId())))
    shared = intersect(alive(e), alive(g))
    gonly = [(y, w) for (y, w) in keys(u.og.edges) if y != w && y in shared && w in shared &&
             !PG.has_edge(e.og, y, w) && PG.has_edge(g.og, y, w)]
    isempty(gonly) && return
    # la cascada del pin en a, con una instantánea por vuelta
    h = deepcopy(u)
    snaps = Any[]
    gset = Set(gonly)
    Probes.with(:review_round => gg -> push!(snaps, (alive(gg), deepcopy(gg.og))),
                :pair_bad => (og, x, w) -> begin
                    p = (x, w) in gset ? (x, w) : ((w, x) in gset ? (w, x) : nothing)
                    p === nothing && return
                    bad = [l for l in 0:u.current_step-1 if isempty(common(og, x, w, l))]
                    for l in bad
                        tag = l == k ? "k" : (l == u.current_step - 1 ? "cima" : (l < k ? "l<k" : "l>k"))
                        CUT[tag] = get(CUT, tag, 0) + 1
                    end
                    CUTN[] += 1
                end) do
        GraphPath.filter!(h, SetNodesId([a]))
    end
    push!(snaps, (alive(h), deepcopy(h.og)))
    # para cada pareja, la primera instantánea sin ella y la causa, vista en la anterior
    rows = Any[]
    for (y, w) in gonly
        prev = nothing; cause = "sobrevive"
        for (i, (A, og)) in enumerate(snaps)
            if !(PG.has_edge(og, y, w))
                if !(y in A) || !(w in A)
                    cause = "node"
                elseif prev !== nothing
                    pog = prev[2]
                    bad = [l for l in 0:u.current_step-1 if isempty(common(pog, y, w, l))]
                    if isempty(bad)
                        # en e: pasos donde y, w no tienen testigo común (por qué e no tiene la pareja)
                        le = [l for l in 0:u.current_step-1 if isempty(common(e.og, y, w, l))]
                        if isempty(le)
                            cause = "otra: e con testigos en todo paso"
                        else
                            l = first(le)
                            tag = l == k ? "k" : (l == u.current_step - 1 ? "cima" : (l < k ? "l<k" : "l>k"))
                            # en la unión, sus testigos en l: ¿por parejas solo-de-g?
                            ws = common(u.og, y, w, l)
                            viag = all(r -> !(PG.has_edge(e.og, y, r) && PG.has_edge(e.og, w, r)), ws)
                            # ¿las parejas no-de-e que lo sostienen en l son P1 (solo testigos del otro color en k)?
                            isP1(p, q) = !PG.has_edge(e.og, p, q) &&
                                all(r -> r.id != a, common(u.og, p, q, k))
                            dep = all(r -> (!PG.has_edge(e.og, y, r) && isP1(y, r)) || (!PG.has_edge(e.og, w, r) && isP1(w, r)), ws)
                            cause = "otra: sin testigo en e en " * tag * (viag ? ", en la unión solo por parejas no-de-e" : ", con testigo en e?!") *
                                    (dep ? "; todas sostenidas por P1" : "; alguna sostenida por no-P1")
                        end
                    else
                        l = first(bad)
                        tag = l == k ? "k" : (l == u.current_step - 1 ? "cima" : "l<k")
                        # de qué lado eran los testigos que tenía en la unión en ese paso
                        ws = common(u.og, y, w, l)
                        sides = join(sort(unique([(PG.has_edge(e.og, y, r) && PG.has_edge(e.og, w, r)) ? "e" :
                                                  (PG.has_edge(g.og, y, r) && PG.has_edge(g.og, w, r)) ? "g" : "mixto"
                                                  for r in ws])), "+")
                        cause = "pair@" * tag * "[" * sides * "]"
                    end
                else
                    cause = "filtro"
                end
                break
            end
            prev = (A, og)
        end
        CAUSES[cause] = get(CAUSES, cause, 0) + 1
        push!(rows, (y, w, cause))
    end
    push!(CASES, (n = length(alive(u)), k = k, a = a, T = u.current_step, gonly = rows, rounds = length(snaps)))
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    machine = SatMachine.new(loader(CNF))
    Probes.with(:join_pre => (x, y) -> (SIDES[] = (deepcopy(x), deepcopy(y))), :join_post => on_join_post) do
        redirect_stdout(devnull) do
            SatMachine.run!(machine)
        end
    end
    println("joins con parejas solo-de-g: $(length(CASES)); parejas: $(sum(length(c.gonly) for c in CASES; init = 0))")
    println("cortes por la regla de parejas: $(CUTN[]); pasos sin testigo en el corte: ", join(["$(k) $(v)" for (k, v) in sort(collect(CUT), by = x -> -last(x))], ", "))
    println("causas: ", join(["$(k) $(v)" for (k, v) in sort(collect(CAUSES), by = x -> -last(x))], ", "))
    sort!(CASES, by = c -> c.n)
    for c in CASES[1:min(NCASES, end)]
        println("== caso: paso actual $(c.T), remitente k = $(c.k), color fijado $(c.a), vivos $(c.n), vueltas $(c.rounds)")
        for (y, w, cause) in c.gonly
            println("   ", key(y), " — ", key(w), ": ", cause)
        end
    end
end

main()
