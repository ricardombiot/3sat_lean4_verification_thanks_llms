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
# Con PURE=1, además, para tríos de cadena de E (hasta MAXT por entrada) que son triángulo en D y triángulo en alguna
# de las dos llegadas que formaron D (triángulo "de un solo lado"):
#   pure        cuántos
#   pure_forb   de ellos, prohibidos en E (HMixed dice que ninguno)
#   pure_cl     hay una camarilla de D por los tres con el valor del literal de E
#   pure_nocl   no la hay
#   pure_any    no la hay con ese valor, pero sí con el otro
#   pure_unk    la búsqueda agotó su presupuesto
#   pure_other  (de pure_nocl) el otro remitente sí tiene una camarilla por los tres con el valor del literal de E
#   pure_none   (de pure_nocl) ningún remitente la tiene
#   pure_arr    hay una camarilla de alguna llegada de E (hasta su cima) por los tres
#   pure_noarr  no la hay
# El papel de la cadena (CHAIN=1), separando los casos con camarilla en D (cl_*) y sin ella (nocl_*):
#   *_topD / *_topO     la cima de la cadena viene de D / del otro remitente
#   *_reach             la cadena baja hasta el paso del literal
#   *_litD / *_litO     (si baja) su nodo del paso del literal es vecino de los tres en D / en el otro remitente
# Por trío de un solo lado (una vez, CHAIN=1), en la llegada A de E que contiene la cima t de la cadena:
#   top_tri   el trío es triángulo en A;   top_k4   además t es vecino de los tres en A
#   top_cl3   hay camarilla de A por el trío;   top_cl4   hay camarilla de A por el trío y t

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
const PURE = get(ENV, "PURE", "0") == "1"
const MAXT = parse(Int, get(ENV, "MAXT", "300"))
const CHAIN = get(ENV, "CHAIN", "0") == "1"

# ¿Hay una camarilla de D (un nodo por paso, vecinos dos a dos) por los nodos de `must`, con el nodo del paso del
# literal de índice `li` (o cualquiera si li < 0)? `nothing` si se agota el presupuesto.
function clique_through(D, must, ls, li; budget = 20000)
    top = Int(D.current_step) - 1
    mustat = Dict(Int(m.id.step) => m for m in must)
    chosen = PathNodeId[]
    b = Ref(budget)
    function go(k)
        b[] -= 1
        b[] < 0 && return false
        k < 0 && return true
        cands = haskey(mustat, k) ? [mustat[k]] : alive_at(D, k)
        for c in cands
            PG.is_alive(D.og, c) || continue
            (k == ls && li >= 0 && Int(c.id.index) != li) && continue
            all(w -> PG.has_edge(D.og, c, w), chosen) || continue
            all(w -> w == c || PG.has_edge(D.og, c, w), must) || continue
            push!(chosen, c)
            r = go(k - 1)
            pop!(chosen)
            r && return true
            b[] < 0 && return false
        end
        return false
    end
    r = go(top)
    return b[] < 0 ? nothing : r
end
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
    pseen = Set{Any}()
    li = Int(s.map_parent_id.index)
    function dfs(x)
        leaves[] > CAP && return
        push!(chain, x)
        k = length(chain)
        for i in 1:k-1, j in i+1:k-1
            a, b = chain[i], chain[j]
            if PURE && length(pseen) < MAXT
                pk = Set((a, b, x))
                if !(pk in pseen)
                    push!(pseen, pk)
                    if CHAIN && any(D -> status(D, a, b, x) in ("T", "F") &&
                            any(B -> B.map_parent_id == D.map_parent_id && status(B, a, b, x) in ("T", "F"), PREVARR), PREV)
                        tp = chain[1]
                        As = [A for A in ARR if A.map_parent_id == s.map_parent_id && PG.is_alive(A.og, tp)]
                        if !isempty(As)
                            A = As[1]
                            if status(A, a, b, x) in ("T", "F")
                                bump(:top_tri)
                                all(u -> PG.has_edge(A.og, tp, u), (a, b, x)) && bump(:top_k4)
                            elseif get(ENV, "DUMP", "0") == "1"
                                sid(z) = "$(Int(z.id.step)):$(Int(z.id.index))<$(z.parent_id === nothing ? "-" : Int(z.parent_id.index))"
                                prior = false
                                n = length(chain)
                                for i1 in 1:n, i2 in i1+1:n, i3 in i2+1:n
                                    (chain[i1], chain[i2], chain[i3]) == (a, b, x) && continue
                                    i3 < n || continue
                                    PG.dead_trio(s.og, chain[i1], chain[i2], chain[i3]) && (prior = true)
                                end
                                Ao = [A2 for A2 in ARR if A2.map_parent_id == s.map_parent_id && A2 !== A]
                                println(stderr, "EXC lit=", LIT[], " top=", sid(tp), " trio=", sid.((a, b, x)),
                                    " chainsteps=", [Int(w.id.step) for w in chain],
                                    " forbE=", PG.dead_trio(s.og, a, b, x), " priorForb=", prior,
                                    " Atop=", status(A, a, b, x), " Aother=", [status(A2, a, b, x) for A2 in Ao],
                                    " edgesAtop=", [PG.has_edge(A.og, u, v) for (u, v) in ((a, b), (a, x), (b, x))],
                                    " topAdjAtop=", [PG.has_edge(A.og, tp, u) for u in (a, b, x)])
                            end
                            clique_through(A, [a, b, x], -1, -1) === true && bump(:top_cl3)
                            clique_through(A, unique([tp, a, b, x]), -1, -1) === true && bump(:top_cl4)
                            bump(:top_n)
                        end
                    end
                    for D in PREV
                        status(D, a, b, x) in ("T", "F") || continue
                        bs = [B for B in PREVARR if B.map_parent_id == D.map_parent_id]
                        any(B -> status(B, a, b, x) in ("T", "F"), bs) || continue
                        bump(:pure)
                        PG.dead_trio(s.og, a, b, x) && bump(:pure_forb)
                        arrs = [A for A in ARR if A.map_parent_id == s.map_parent_id]
                        ra = [clique_through(A, [a, b, x], -1, -1) for A in arrs]
                        any(==(true), ra) ? bump(:pure_arr) : bump(:pure_noarr)
                        r = clique_through(D, [a, b, x], LIT[], li)
                        if CHAIN && r !== nothing
                            pre = r ? "cl_" : "nocl_"
                            others = [D2 for D2 in PREV if D2 !== D]
                            tp = chain[1]
                            bump(Symbol(pre, tp.parent_id == D.map_parent_id ? "topD" : "topO"))
                            cs = [w for w in chain if Int(w.id.step) == LIT[]]
                            if !isempty(cs)
                                bump(Symbol(pre, "reach"))
                                w = cs[1]
                                all(u -> PG.has_edge(D.og, w, u), (a, b, x)) && bump(Symbol(pre, "litD"))
                                any(D2 -> all(u -> PG.has_edge(D2.og, w, u), (a, b, x)), others) &&
                                    bump(Symbol(pre, "litO"))
                            end
                        end
                        if r === nothing
                            bump(:pure_unk)
                        elseif r
                            bump(:pure_cl)
                        else
                            bump(:pure_nocl)
                            r2 = clique_through(D, [a, b, x], LIT[], 1 - li)
                            r2 === true && bump(:pure_any)
                            others = [D2 for D2 in PREV if D2 !== D]
                            if any(D2 -> clique_through(D2, [a, b, x], LIT[], li) === true, others)
                                bump(:pure_other)
                            else
                                bump(:pure_none)
                            end
                        end
                    end
                end
            end
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
            :Fsrc_one, :Fsrc_open, :pure, :pure_forb, :pure_cl, :pure_nocl, :pure_any, :pure_unk, :pure_other, :pure_none, :pure_arr, :pure_noarr,
            :cl_topD, :cl_topO, :cl_reach, :cl_litD, :cl_litO, :nocl_topD, :nocl_topO, :nocl_reach, :nocl_litD,
            :nocl_litO, :top_n, :top_tri, :top_k4, :top_cl3, :top_cl4, :cap)
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
