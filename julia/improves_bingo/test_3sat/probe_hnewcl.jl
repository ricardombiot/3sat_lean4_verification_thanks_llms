# HNew en las líneas de cláusula con dos remitentes (30-sept-2026, rama reader-stuck; lean PreClause.lean).
#
#   PROBE_MAP=bin PROBE_ONLY=clause_mix.cnf,... julia --project=. test_3sat/probe_hnewcl.jl <salida.tsv>
#
# Con FORBID = :on. En cada línea de cláusula con dos remitentes, para cada entrada E y cada trío prohibido de una
# cadena de E (sin repetir), se mira cómo lo corta cada remitente D:
#   n_top   falta un nodo del paso de la cima de E (nunca vive en D)
#   n_stop  falta un nodo del paso de la cima de D (la cima del otro remitente)
#   n_low   falta un nodo más abajo
#   m_stop  todos vivos, falta una arista con un nodo de la cima de D
#   m_low   todos vivos, falta una arista entre nodos más abajo
#   F_pre   triángulo prohibido en D, con todos sus nodos a la altura del paso de variable del literal o por debajo
#   F_post  triángulo prohibido en D, con algún nodo por encima de ese paso
#   T       abierto en D (contraejemplo de HNew)
# Y para los casos F (triángulo prohibido en D), el estado del trío en las dos llegadas que formaron D:
#   Fsrc_fresh  no es triángulo en ninguna de las dos (triángulo mezclado del join de D: prohibido por definición)
#   Fsrc_rec    prohibido en alguna de ellas (viene de más abajo)
#   Fsrc_one    solo había una llegada en D
#   Fsrc_open   abierto en alguna (imposible si D lo prohíbe por su join)

const OUT = abspath(ARGS[1])
const CAP = 20000
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)

alive_at(g, l) = collect(get(g.og.alive, l, SetPathNodesId()))
adj(g, a, b) = a == b ? PG.is_alive(g.og, a) : PG.has_edge(g.og, a, b)

const LIT = Ref(-1)
const PREV = Any[]
const PREVARR = Any[]      # las llegadas que formaron las entradas de PREV
const ARR = Any[]
using .AbsSat.Probes
status(g, a, b, x) = !(PG.is_alive(g.og, a) && PG.is_alive(g.og, b) && PG.is_alive(g.og, x)) ? "n" :
    !(PG.has_edge(g.og, a, b) && PG.has_edge(g.og, a, x) && PG.has_edge(g.og, b, x)) ? "m" :
    PG.dead_trio(g.og, a, b, x) ? "F" : "T"
function src(D, a, b, x)
    bs = [B for B in PREVARR if B.map_parent_id == D.map_parent_id]
    length(bs) == 1 && return :Fsrc_one
    st = [status(B, a, b, x) for B in bs]
    any(==("T"), st) && return :Fsrc_open
    any(==("F"), st) && return :Fsrc_rec
    return :Fsrc_fresh
end

function classify(D, top, a, b, x)
    tri = (a, b, x)
    stepof(z) = Int(z.id.step)
    if !all(z -> PG.is_alive(D.og, z), tri)
        miss = [z for z in tri if !PG.is_alive(D.og, z)]
        any(z -> stepof(z) == top, miss) && return :n_top
        any(z -> stepof(z) == top - 1, miss) && return :n_stop
        return :n_low
    end
    pairs = ((a, b), (a, x), (b, x))
    missing_e = [p for p in pairs if !PG.has_edge(D.og, p[1], p[2])]
    if !isempty(missing_e)
        any(p -> stepof(p[1]) == top - 1 || stepof(p[2]) == top - 1, missing_e) && return :m_stop
        return :m_low
    end
    if PG.dead_trio(D.og, a, b, x)
        vs = isodd(LIT[]) ? LIT[] : LIT[] - 1
        return maximum(stepof.(tri)) <= vs ? :F_pre : :F_post
    end
    return :T
end

function scan(s)
    top = Int(s.current_step) - 1
    leaves = Ref(0)
    chain = PathNodeId[]
    seen = Set{Any}()
    function dfs(x)
        leaves[] > CAP && return
        push!(chain, x)
        k = length(chain)
        for i in 1:k-1, j in i+1:k-1
            a, b = chain[i], chain[j]
            PG.dead_trio(s.og, a, b, x) || continue
            key = Set((a, b, x))
            key in seen && continue
            push!(seen, key)
            bump(:trios)
            for D in PREV
                c = classify(D, top, a, b, x)
                bump(c)
                c in (:F_pre, :F_post) && bump(src(D, a, b, x))
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
    cols = (:lines2, :trios, :n_top, :n_stop, :n_low, :m_stop, :m_low, :F_pre, :F_post, :T, :Fsrc_fresh, :Fsrc_rec,
            :Fsrc_one, :Fsrc_open, :cap)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C); empty!(PREV); empty!(PREVARR); empty!(ARR)
        PG.FORBID[] = :on
        t = @elapsed begin
            machine = SatMachine.new(loader(path))
            redirect_stdout(devnull) do
                SatMachine.init!(machine)
                while true
                    gs = [g for g in SatMachine.get_gpath_list(machine) if g.is_valid]
                    if !isempty(gs) && length(PREV) == 2
                        ttl = SatMachine.map_get_node(machine.gmap, gs[1].map_parent_id).title
                        if startswith(ttl, "or")
                            rq = SatMachine.map_get_node(machine.gmap, gs[1].map_parent_id).requires
                            LIT[] = isempty(rq) ? -1 : Int(first(rq).step)
                            bump(:lines2)
                            foreach(scan, gs)
                        end
                    end
                    (SatMachine.is_finished(machine) || !SatMachine.have_gpaths_step(machine)) && break
                    empty!(PREV); append!(PREV, [deepcopy(g) for g in gs])
                    empty!(PREVARR); append!(PREVARR, ARR)
                    empty!(ARR)
                    Probes.with(:up_done => g -> push!(ARR, deepcopy(g))) do
                        SatMachine.make_step!(machine)
                    end
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
