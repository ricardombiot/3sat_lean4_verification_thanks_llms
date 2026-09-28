# El orden de la cascada en la estrella (28-sept-2026; informe v203 §6, paso 3; lean/improves_bingo StarLocal.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_starorder.jl <salida.tsv> [muestras] [semilla]
#
# En cada join, U fijada en P (h) y el lado S de cada cima t fijado en P (hS). W = estrella de t en h. Parejas del otro
# lado F: aristas de h entre nodos de W que hS no tiene. Para f = (x, z) ∈ F, un paso l es un hueco si ningún w ∈ W en
# l tiene aristas de hS con x y con z. Un hueco l «baja» para un orden < si todo testigo w ∈ W en l (aristas de h con x
# y con z) forma con x o con z una pareja de F menor que f. Si con un orden toda f de F tiene un hueco que baja, la
# inducción bien fundada cierra: ninguna estructura cerrada dentro de la estrella contiene parejas del otro lado.
#   one — parejas de F; nogap — sin hueco (StarGap: 0)
#   bad_A — sin hueco que baje con A = (paso más alto, paso más bajo) creciente (lexicográfico)
#   bad_B — con B = (paso más bajo, paso más alto) creciente
#   bad_C — con C = paso más alto decreciente, luego paso más bajo creciente
#   bad_D — con D = paso más alto decreciente, luego paso más bajo decreciente
#   low   — parejas de F sin hueco por encima (el 5 % de probe_stargap.jl)
#   noauto — parejas de F sin hueco «automático»: por debajo de su paso más bajo, o en el paso de origen (c-2).
#            Con el orden A, un hueco por debajo baja siempre (las dos parejas posibles son menores), y en el origen no
#            hay testigos de la unión (los padres de la cima solo tienen aristas del lado). Si noauto = 0, la inducción
#            cierra con StarGapLow, una propiedad del lado solo.
#   Para las de noauto, el primer hueco que baja con A, por tipo:
#     k_uempty — en ese paso no hay ningún testigo de U en la estrella (la pareja cae de golpe también en U)
#     k_midlow — hueco entre sus pasos y todo testigo forma la pareja del otro lado con el extremo más bajo
#     k_other  — otro caso
#   e_pairs / e_noauto — lo mismo para TODAS las parejas de la estrella del lado que el lado no hace poseerse
#            (StarGapLow como propiedad de un estado)

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 2
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(SEED))
const TOT = Dict{Symbol, Int}()
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)

function pinned(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(P))
    return g2
end
pinned_edges(h) = h.is_valid ? Set(keys(h.og.edges)) : Set{Tuple{PathNodeId, PathNodeId}}()

function samplesP(g0)
    steps = choice_steps(g0.og)
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    isempty(steps) && return Ps
    for _ in 1:SAMPLES
        m = rand(RNG[], 1:min(2, length(steps)))
        push!(Ps, [rand(RNG[], map_nodes(g0.og, s)) for s in shuffle(RNG[], steps)[1:m]])
    end
    return Ps
end

hi(f) = max(f[1].id.step, f[2].id.step)
lo(f) = min(f[1].id.step, f[2].id.step)
const ORDERS = Dict(
    :A => (a, b) -> (hi(a), lo(a)) < (hi(b), lo(b)),
    :B => (a, b) -> (lo(a), hi(a)) < (lo(b), hi(b)),
    :C => (a, b) -> (-hi(a), lo(a)) < (-hi(b), lo(b)),
    :D => (a, b) -> (-hi(a), -lo(a)) < (-hi(b), -lo(b)))

function measure!(e, g)
    c = e.current_step
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    for P in samplesP(u)
        h = pinned(u, P)
        h.is_valid || continue
        hs = Dict(true => pinned(e, P), false => pinned(g, P))
        for t in collect(get(h.og.alive, c - 1, SetPathNodesId()))
            hS = hs[PG.is_alive(e.og, t)]
            hS.is_valid || continue
            W = Set(PG.neighbors_all(h.og, t)); push!(W, t)
            eS(a, b) = PG.is_alive(hS.og, a) && PG.is_alive(hS.og, b) && PG.has_edge(hS.og, a, b)
            F = Set{Tuple{PathNodeId, PathNodeId}}()
            for x in W, z in PG.neighbors_all(h.og, x)
                (z != x && z in W) || continue
                eS(x, z) || push!(F, PG.edge_key(x, z))
            end
            inF(a, b) = PG.edge_key(a, b) in F
            # StarGapLow en el lado solo: todas las parejas de su estrella que no se poseen
            WS = Set(PG.neighbors_all(hS.og, t)); push!(WS, t)
            WSv = collect(WS)
            for i in eachindex(WSv), j in i+1:length(WSv)
                x, z = WSv[i], WSv[j]
                (x == t || z == t || eS(x, z) || x.id.step == z.id.step) && continue
                bump!(:e_pairs)
                ff = (x, z)
                okl = any(l -> (l < lo(ff) || l == c - 2) && l != x.id.step && l != z.id.step &&
                          !any(w -> w in WS && eS(x, w) && eS(z, w), get(hS.og.alive, l, SetPathNodesId())), 0:c-1)
                okl || bump!(:e_noauto)
            end
            for f in F
                bump!(:one)
                x, z = f
                gaps = [l for l in 0:c-1 if l != x.id.step && l != z.id.step &&
                        !any(w -> w in W && eS(x, w) && eS(z, w), get(h.og.alive, l, SetPathNodesId()))]
                isempty(gaps) && (bump!(:nogap); continue)
                any(l -> l > hi(f), gaps) || bump!(:low)
                if !any(l -> l < lo(f) || l == c - 2, gaps)
                    bump!(:noauto)
                    zlow = x.id.step < z.id.step ? x : z
                    xhigh = zlow == x ? z : x
                    wits(l) = [w for w in get(h.og.alive, l, SetPathNodesId()) if w in W && PG.has_edge(h.og, x, w) && PG.has_edge(h.og, z, w)]
                    goodA(l) = all(w -> (inF(x, w) && ORDERS[:A](PG.edge_key(x, w), f)) || (inF(z, w) && ORDERS[:A](PG.edge_key(z, w), f)), wits(l))
                    gl = findfirst(goodA, gaps)
                    if gl === nothing
                        bump!(:k_none)
                    else
                        l = gaps[gl]
                        ws = wits(l)
                        if isempty(ws)
                            bump!(:k_uempty)
                        elseif lo(f) < l < hi(f) && all(w -> inF(zlow, w), ws)
                            bump!(:k_midlow)
                        else
                            bump!(:k_other)
                        end
                    end
                end
                for (name, lt) in ORDERS
                    ok = any(gaps) do l
                        all(w -> !(w in W && PG.has_edge(h.og, x, w) && PG.has_edge(h.og, z, w)) ||
                                 (inF(x, w) && lt(PG.edge_key(x, w), f)) || (inF(z, w) && lt(PG.edge_key(z, w), f)),
                            get(h.og.alive, l, SetPathNodesId()))
                    end
                    ok || bump!(Symbol(:bad_, name))
                end
            end
        end
    end
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            $(measure!)(gpath, gpath_inmutable)
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
        end
    end
end)

const COLS = (:one, :nogap, :low, :noauto, :k_uempty, :k_midlow, :k_other, :k_none, :bad_A, :bad_B, :bad_C, :bad_D, :e_pairs, :e_noauto)

function corpus()
    dirs = [joinpath(ROOT, "test/example_cnf"), joinpath(ROOT, "test_window/instances"),
            joinpath(ROOT, "test_3sat/output/instances"), joinpath(ROOT, "test_3sat/output_test1/instances"),
            joinpath(ROOT, "test_3sat/output_test2/instances"), joinpath(ROOT, "test_3sat/output_test3/instances"),
            joinpath(ROOT, "../../lean/improves_bin/cnf/crafted")]
    files = String[]
    for d in dirs
        isdir(d) || continue
        for f in sort(readdir(d))
            endswith(f, ".cnf") && f != "tseitin_petersen_H.cnf" && push!(files, joinpath(d, f))
        end
    end
    return files
end

function main()
    open(OUT, "w") do io
        println(io, "instance\t" * join(string.(COLS), "\t"))
        for path in corpus()
            name = basename(path)
            empty!(TOT)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch e
                println(io, "$name\tERROR $(typeof(e))"); flush(io); continue
            end
            println(io, "$name\t" * join([string(get(TOT, cc, 0)) for cc in COLS], "\t"))
            flush(io)
        end
    end
end

main()
