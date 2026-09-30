# CrossClosed entre todos los estados de una línea (30-sept-2026, rama reader-stuck; lean LiveJoin.lean).
#
#   ABL=none|noup PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_crossline.jl <salida.tsv>
#
# Con FORBID = :on. La máquina paso a paso; en cada línea, para cada par ordenado (A, B) de entradas válidas distintas:
# se recorren las cadenas de A (de una cima abajo por padres vivos, vecinos dos a dos) y, para cada trío de la cadena
# prohibido en A, se mira si B lo tiene abierto (triángulo sin prohibir).
#   lines, pairs, bad (tríos prohibidos en cadenas), open (abiertos en el otro estado), cap

const OUT = abspath(ARGS[1])
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)

const ABL = get(ENV, "ABL", "none")
if ABL in ("noup", "noboth")
    Core.eval(PathOwnersGraph, :(up_forbid!(g :: OwnersGraph, n :: PathNodeId, parents) = nothing))
end

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
adj(g, a, b) = a == b ? PG.is_alive(g.og, a) : PG.has_edge(g.og, a, b)
isopen(o, a, b, x) = PG.has_edge(o.og, a, b) && PG.has_edge(o.og, a, x) && PG.has_edge(o.og, b, x) &&
                     !PG.dead_trio(o.og, a, b, x)

const KIND = Ref("?")
const LIT = Ref(-1)        # paso del literal que fijan los requisitos de la línea (cláusula)
const DIST = Dict{Int, Int}()
const ARR = Any[]          # llegadas del último paso (copias en :up_done)
const PAT = Dict{String, Int}()
const PREV = Any[]         # entradas de la línea anterior (los remitentes)
const TRANS = Dict{String, Int}()   # remitente → llegada, por remitente, en los tríos prohibidos de cadenas
using .AbsSat.Probes
status(g, a, b, x) = !(PG.is_alive(g.og, a) && PG.is_alive(g.og, b) && PG.is_alive(g.og, x)) ? "n" :
    !(PG.has_edge(g.og, a, b) && PG.has_edge(g.og, a, x) && PG.has_edge(g.og, b, x)) ? "m" :
    PG.dead_trio(g.og, a, b, x) ? "F" : "T"
# patrón: para las llegadas al destino de s (el estado con el trío prohibido) y al de o, por remitente
function pattern(s, o, a, b, x)
    function skey(g)
        xs = alive_at(g, Int(g.current_step) - 1)
        isempty(xs) || first(xs).parent_id === nothing ? "?" : string(first(xs).parent_id.index)
    end
    part(dest) = join(sort([skey(g) * status(g, a, b, x) for g in ARR if g.map_parent_id == dest]), ",")
    "s:" * part(s.map_parent_id) * " o:" * part(o.map_parent_id)
end
function cross(s, o)
    top = Int(s.current_step) - 1
    leaves = Ref(0)
    chain = PathNodeId[]
    function dfs(x)
        leaves[] > CAP && return
        push!(chain, x)
        k = length(chain)
        for i in 1:k-1, j in i+1:k-1
            a, b = chain[i], chain[j]
            if KIND[] == "cl" && !isempty(PREV)
                for D in PREV
                    status(D, a, b, x) == "T" || continue
                    for A in ARR
                        A.map_parent_id == s.map_parent_id || continue
                        xs = alive_at(A, Int(A.current_step) - 1)
                        (isempty(xs) || first(xs).parent_id != D.map_parent_id) && continue
                        bump(:all_Dopen)
                        status(A, a, b, x) == "T" || bump(:all_Dopen_Aclosed)
                    end
                end
            end
            PG.dead_trio(s.og, a, b, x) || continue
            bump(:bad); bump(Symbol("bad_", KIND[]))
            if !isempty(PREV)
                opens = [status(D, a, b, x) == "T" for D in PREV]
                any(opens) ? bump(Symbol("sender_open_", KIND[])) : bump(Symbol("sender_closed_", KIND[]))
                for D in PREV
                    kD = D.map_parent_id
                    for A in ARR
                        A.map_parent_id == s.map_parent_id || continue
                        xs = alive_at(A, Int(A.current_step) - 1)
                        (isempty(xs) || first(xs).parent_id != kD) && continue
                        tk = KIND[] * " D:" * status(D, a, b, x) * "→A:" * status(A, a, b, x)
                        TRANS[tk] = get(TRANS, tk, 0) + 1
                    end
                end
            end
            isopen(o, a, b, x) && bump(:open)
            # por qué está cortado en el otro: falta un nodo, falta una arista entre vivos, o está prohibido
            if !(PG.is_alive(o.og, a) && PG.is_alive(o.og, b) && PG.is_alive(o.og, x))
                bump(Symbol("why_node_", KIND[]))
            elseif !(PG.has_edge(o.og, a, b) && PG.has_edge(o.og, a, x) && PG.has_edge(o.og, b, x))
                bump(Symbol("why_edge_", KIND[]))
            else
                bump(Symbol("why_forb_", KIND[]))
            end
            if KIND[] == "cl" && PG.is_alive(o.og, a) && PG.is_alive(o.og, b) && PG.is_alive(o.og, x)
                lo = minimum(Int(z.id.step) for z in (a, b, x))
                DIST[lo - LIT[]] = get(DIST, lo - LIT[], 0) + 1
                pk = pattern(s, o, a, b, x); PAT[pk] = get(PAT, pk, 0) + 1
            end
        end
        if Int(x.id.step) > 0
            nd = PathCollectionLines.get_node(s.table_lines, x)
            if nd !== nothing
                for p in nd.parents
                    PG.is_alive(s.og, p) && all(w -> adj(s, w, p), chain) && dfs(p)
                end
            end
        else
            leaves[] += 1
        end
        pop!(chain)
    end
    foreach(dfs, alive_at(s, top))
    leaves[] > CAP && bump(:cap)
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:all_Dopen, :all_Dopen_Aclosed, :sender_open_cl, :sender_closed_cl, :lines, :lines_var, :lines_neg, :lines_cl, :lines_fus, :bad_fus, :why_node_fus, :why_edge_fus, :why_forb_fus, :pairs, :bad, :open, :bad_var, :bad_neg, :bad_cl, :why_node_var, :why_node_neg, :why_node_cl, :why_edge_var, :why_edge_neg, :why_edge_cl, :why_forb_var, :why_forb_neg, :why_forb_cl, :cap)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(DIST); empty!(PAT); empty!(PREV); empty!(TRANS)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.init!(machine)
                while true
                    gs = [g for g in SatMachine.get_gpath_list(machine) if g.is_valid]
                    bump(:lines)
                    if !isempty(gs)
                        ttl = SatMachine.map_get_node(machine.gmap, gs[1].map_parent_id).title
                        KIND[] = startswith(ttl, "or") ? "cl" : startswith(ttl, "!") ? "neg" :
                                 occursin("Fusion", ttl) ? "fus" : "var"
                        bump(Symbol("lines_", KIND[]))
                        rq = SatMachine.map_get_node(machine.gmap, gs[1].map_parent_id).requires
                        LIT[] = isempty(rq) ? -1 : Int(first(rq).step)
                        C[Symbol("title_", KIND[])] = 1
                    end
                    for A in gs, B in gs
                        A === B && continue
                        bump(:pairs)
                        cross(A, B)
                    end
                    (SatMachine.is_finished(machine) || !SatMachine.have_gpaths_step(machine)) && break
                    empty!(PREV); append!(PREV, [deepcopy(g) for g in gs])
                    empty!(ARR)
                    Probes.with(:up_done => g -> push!(ARR, deepcopy(g))) do
                        SatMachine.make_step!(machine)
                    end
                end
            end
        end
        PG.FORBID[] = :off
        println(stderr, basename(path), " remitente→llegada => ", sort(collect(TRANS)))
        println(stderr, basename(path), " patrones (estado de cada llegada: T abierto, F prohibido, m falta arista, n falta nodo) => ", sort(collect(PAT)))
        println(stderr, basename(path), " distancia (paso más bajo del trío − paso del literal) => casos: ", sort(collect(DIST)))
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
