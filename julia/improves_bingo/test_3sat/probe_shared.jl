# Posesiones entre nodos compartidos en los joins (29-sept-2026, rama reader-stuck; Lean `NodeIn.lean`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_shared.jl <salida.tsv>
#
# En cada join de dos lados e (color a) y g (color s) en el paso del remitente k = T - 2:
#   shared   — nodos vivos en los dos lados
#   g_only   — posesiones entre compartidos que tiene g y no e (e_only, al revés)
#   wa_t / wa_f — WitnessAgree: para una posesión y–w de g entre compartidos, si en e los dos poseen un mismo nodo r
#                 del color a en k, ¿se poseen en e? (wa_f: no). Y al revés, con s y g.
#   se_t / se_f — SideEdgesAt directa: parejas de la unión fijada en a (en s) que no son posesiones de e (de g)
#   ab_t / ab_f — la unión fijada en el color de un lado es (no es) ese lado revisado (vivos y aristas)
#   use_a / use_s — posesiones solo-de-g (solo-de-e) que siguen en la unión fijada en a (en s): si se usan

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
pin(g, P) = (g2 = deepcopy(g); GraphPath.filter!(g2, SetNodesId(P)); g2)

const SIDES = Ref{Any}(nothing)

function side_check!(A, B, colA, k, tag_t, tag_f)
    # posesiones de B entre compartidos que A no tiene; WitnessAgree con testigos del color de A en A
    shared = intersect(alive(A), alive(B))
    Ka = [r for r in get(A.og.alive, k, SetPathNodesId()) if r.id == colA]
    for (y, w) in keys(B.og.edges)
        (y == w || !(y in shared) || !(w in shared)) && continue
        PG.has_edge(A.og, y, w) && continue
        bump(tag_t == :wa_t ? :g_only : :e_only)
        if any(r -> PG.has_edge(A.og, y, r) && PG.has_edge(A.og, w, r), Ka)
            bump(tag_f)
        end
        bump(tag_t)
    end
    return shared
end

function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    k = u.current_step - 2
    k >= 0 || return
    cols = unique(x.id for x in get(u.og.alive, k, SetPathNodesId()))
    length(cols) == 2 || return
    a = first(unique(x.id for x in get(e.og.alive, k, SetPathNodesId())))
    s = first(filter(!=(a), cols))
    bump(:joins)
    shared = side_check!(e, g, a, k, :wa_t, :wa_f)
    side_check!(g, e, s, k, :wb_t, :wb_f)
    bump(:shared, length(shared))
    for (c, side, other, tu) in ((a, e, g, :use_a), (s, g, e, :use_s))
        h = pin(u, [c])
        # Absorb de estado: la unión fijada en el color de un lado es ese lado revisado
        hs = pin(side, [c])
        bump(:ab_t)
        same = h.is_valid == hs.is_valid && (!h.is_valid || (alive(h) == alive(hs) && Set(keys(h.og.edges)) == Set(keys(hs.og.edges))))
        same || bump(:ab_f)
        h.is_valid || continue
        for (y, w) in keys(h.og.edges)
            y == w && continue
            bump(:se_t)
            PG.has_edge(side.og, y, w) || bump(:se_f)
            (y in shared && w in shared && !PG.has_edge(side.og, y, w) && PG.has_edge(other.og, y, w)) && bump(tu)
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :shared, :g_only, :e_only, :wa_t, :wa_f, :wb_t, :wb_f, :se_t, :se_f, :use_a, :use_s, :ab_t, :ab_f)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b))),
                                 :join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
