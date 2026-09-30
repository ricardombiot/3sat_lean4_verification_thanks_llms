# (★) en el join: toda cadena viva de la unión es viva en el lado de su cima (30-sept-2026, rama reader-stuck).
#
#   ABL=none|noup|nojoin|noboth PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_joinside.jl <salida.tsv>
#
# Con FORBID = :on. En cada join (puntos :join_pre / :join_post) se guardan los dos lados y se recorren todas las
# cadenas vivas de la unión (de una cima hacia abajo por padres vivos, vecinos dos a dos, sin trío prohibido en la
# unión). Para cada cadena, el lado de su cima (el único donde la cima está viva) y:
#   chains            — cadenas vivas de la unión (prefijos incluidos: cada nodo añadido cuenta)
#   top_both          — cimas vivas en los dos lados (se espera 0)
#   v_node, v_edge    — un nodo de la cadena no está vivo / una pareja no es arista en el lado de la cima
#   v_trio_t          — un trío con la cima está prohibido en el lado (se espera 0: la unión lo prohibiría)
#   v_trio            — un trío sin la cima está prohibido en el lado de la cima (el hueco de (★))
#   v_link            — un enlace padre de la cadena no está en el documento del lado
#   dead              — callejones en la unión (control: LiveExt)
#   common_tri, tri_both, tri_disagree — triángulos de los dos lados; prohibidos en los dos; prohibidos en uno solo

const OUT = abspath(ARGS[1])
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
const PRE = Ref{Any}(nothing)

# Ablación (ABL): none | noup (el UP no hereda tríos) | nojoin (el join no guarda ninguno) | noboth
const ABL = get(ENV, "ABL", "none")
if ABL in ("noup", "noboth")
    Core.eval(PathOwnersGraph, :(up_forbid!(g :: OwnersGraph, n :: PathNodeId, parents) = nothing))
end
if ABL in ("nojoin", "noboth")
    Core.eval(PathOwnersGraph, :(join_forbid(ga :: OwnersGraph, gb :: OwnersGraph) = Dict{EdgeKey, SetPathNodesId}()))
end

alive_at(g, l) = sort(collect(get(g.og.alive, l, SetPathNodesId())), by = string)
adj(g, a, b) = a == b ? PG.is_alive(g.og, a) : PG.has_edge(g.og, a, b)
dead(g, a, b, r) = length(unique((a, b, r))) == 3 && PG.has_edge(g.og, a, b) && PG.dead_trio(g.og, a, b, r)

function live_parents(g, x, chain)
    nd = PathCollectionLines.get_node(g.table_lines, x)
    nd === nothing && return PathNodeId[]
    [p for p in nd.parents if PG.is_alive(g.og, p) && all(w -> adj(g, w, p), chain) &&
        !any(dead(g, chain[i], chain[j], p) for i in eachindex(chain) for j in i+1:length(chain))]
end

# ¿la cadena (nuevo nodo al final) es viva en el lado s? se mira solo lo que añade el último nodo
function check_side(s, chain)
    x = chain[end]; k = length(chain)
    PG.is_alive(s.og, x) || (bump(:v_node); return)
    any(w -> !adj(s, w, x), chain) && bump(:v_edge)
    if k >= 2
        nd = PathCollectionLines.get_node(s.table_lines, chain[end-1])
        (nd === nothing || !(x in nd.parents)) && bump(:v_link)
    end
    for i in 1:k-1, j in i+1:k-1
        a, b = chain[i], chain[j]
        (PG.has_edge(s.og, a, b) && PG.has_edge(s.og, a, x) && PG.has_edge(s.og, b, x)) || continue
        if PG.dead_trio(s.og, a, b, x)
            i == 1 ? bump(:v_trio_t) : bump(:v_trio)
        end
    end
end

# ¿coinciden los dos lados en los tríos prohibidos de los triángulos que tienen los dos?
function agree(a, b)
    for (k, e) in a.og.edges
        PG.has_edge(b.og, k[1], k[2]) || continue
        for r in collect(PG.neighbors_all(a.og, k[1]))
            (r == k[1] || r == k[2] || !(PG.node_ord(k[2]) < PG.node_ord(r))) && continue
            (PG.has_edge(a.og, k[2], r) && PG.has_edge(b.og, k[1], r) && PG.has_edge(b.og, k[2], r)) || continue
            bump(:common_tri)
            fa = PG.dead_trio(a.og, k[1], k[2], r); fb = PG.dead_trio(b.og, k[1], k[2], r)
            if fa != fb
                bump(:tri_disagree)
                s1 = fa ? a : b   # el lado que lo prohíbe
                tri = (k[1], k[2], r)
                top = Int(s1.current_step) - 1
                okt = false
                for t in alive_at(s1, top)
                    all(x -> PG.has_edge(s1.og, t, x), tri) || continue
                    bump(:dis_top_adj)
                    if !any(PG.dead_trio(s1.og, t, tri[i], tri[j]) for i in 1:3 for j in i+1:3)
                        okt = true; bump(:dis_top_open)
                    end
                end
                okt && bump(:dis_open)
                # ¿algún nodo del trío es de un solo lado?
                all(x -> PG.is_alive(a.og, x) && PG.is_alive(b.og, x), tri) || bump(:dis_notshared)
            end
            (fa && fb) && bump(:tri_both)
        end
    end
end

function judge(u, sides)
    u.is_valid || return
    bump(:joins)
    agree(sides[1], sides[2])
    top = Int(u.current_step) - 1
    leaves = Ref(0)
    chain = PathNodeId[]
    function dfs(x, s)
        leaves[] > CAP && return
        push!(chain, x)
        bump(:chains)
        check_side(s, chain)
        if Int(x.id.step) == 0
            leaves[] += 1
        else
            ps = live_parents(u, x, chain)
            isempty(ps) ? bump(:dead) : foreach(p -> dfs(p, s), ps)
        end
        pop!(chain)
    end
    for t in alive_at(u, top)
        ins = [s for s in sides if PG.is_alive(s.og, t)]
        length(ins) == 2 && bump(:top_both)
        isempty(ins) && (bump(:top_none); continue)
        dfs(t, ins[1])
    end
    leaves[] > CAP && bump(:cap)
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:joins, :common_tri, :tri_both, :tri_disagree, :dis_top_adj, :dis_top_open, :dis_open, :chains, :top_both, :top_none, :v_node, :v_edge, :v_link, :v_trio_t, :v_trio, :dead, :cap)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            Probes.with(:join_pre => (a, b) -> (PRE[] = (deepcopy(a), deepcopy(b))),
                        :join_post => u -> (PRE[] === nothing || judge(u, PRE[]); PRE[] = nothing)) do
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
