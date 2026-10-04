# Los testigos malos de SplitAt (28-sept-2026; lean/improves_bingo SplitWitness.lean, `WitSplit`).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_badwit.jl <salida.tsv> [muestras] [semilla]
#
# En cada join (U la unión, k = c-2), para P vacío y `muestras` P: h = U fijada en P (review). Para cada nodo del
# mapa b del paso k se vigilan las aristas (y,w) de h (sin extremos en k) que tienen a un nodo de b como testigo
# común en h, y se fija h en b. Las que caen son parejas con un testigo malo. Por cada una:
#   regla (pair, clean, require) y, si es pair, el nivel más alto sin entrada común (0 = cima, 1 = origen, 2 = c-3,
#   ...) y quién lo vació (como probe_side_cascade.jl; `*` = otra arista vigilada);
#   `own` — la pareja es arista del lado de b (el lado que tiene vivo a b) / `other` — no lo es (solo del otro).
#   watched — vigiladas; bad — caídas (con el testigo b malo); good — sobreviven.

using Random

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT = abspath(ARGS[1])
const SAMPLES = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 1
const SEED = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 20260928
include(joinpath(ROOT, "src/main.jl"))

const LOAD = get(ENV, "PROBE_MAP", "bin") == "bin" ? GraphMapBin.load_import_bin! : GraphMap.load_import!

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId

const PG = PathOwnersGraph
const RNG = Ref(MersenneTwister(SEED))
const WATCH = Dict{Tuple{PathNodeId, PathNodeId}, Int}()   # arista vigilada → d
const TALLY = Dict{Tuple{Symbol, Int}, Int}()               # (regla, d) → cuántas
const TOT = Dict{Symbol, Int}()                             # por instancia: joins, watched, left
const LVL = Dict{Int, Int}()                                # nivel más alto sin entrada común → cuántas
const CUR_C = Ref(0)
const COMMON = Dict{Tuple{Tuple{PathNodeId, PathNodeId}, Int}, Set{PathNodeId}}()   # (arista, paso) → C(s)
const INDEX = Dict{Tuple{PathNodeId, PathNodeId}, Vector{Tuple{Tuple{PathNodeId, PathNodeId}, Int}}}()
const EMPTIER = Dict{Tuple{Tuple{PathNodeId, PathNodeId}, Int}, String}()
const CASC = Dict{Tuple{Int, String}, Int}()                                        # (nivel, quién) → cuántas

# Pasos (desde la cima) en que las tablas de x y w no comparten entrada, tras quitar la arista (sus pasos
# propios no cuentan: antes de quitarla compartían x o w).
function fail_levels(g, x, w)
    c = CUR_C[]
    lv = Int[]
    inc_w = g.inc[w]
    for (s, set_x) in g.inc[x]
        (s == x.id.step || s == w.id.step) && continue
        set_w = get(inc_w, s, nothing)
        set_w === nothing && continue
        (isempty(set_x) || isempty(set_w) || !any(id -> id in set_w, set_x)) && push!(lv, (c - 1) - s)
    end
    return lv
end

function track!(k, rule)
    lst = get(INDEX, k, nothing)
    lst === nothing && return
    tag = string(rule) * (haskey(WATCH, k) ? "*" : "")
    for (wk, s) in lst
        C = get(COMMON, (wk, s), nothing)
        C === nothing && continue
        c = k[1] in wk ? k[2] : k[1]
        c in C || continue
        delete!(C, c)
        isempty(C) && !haskey(EMPTIER, (wk, s)) && (EMPTIER[(wk, s)] = tag)
    end
end

function hook(g, k, rule)
    track!(k, rule)
    d = pop!(WATCH, k, nothing)
    d === nothing && return
    key = (rule, min(d, 3))
    TALLY[key] = get(TALLY, key, 0) + 1
    if rule == :pair
        lv = fail_levels(g, k[1], k[2])
        top = isempty(lv) ? -1 : minimum(lv)
        LVL[min(top, 4)] = get(LVL, min(top, 4), 0) + 1
        0 in lv && bump!(:pairtop)
        1 in lv && bump!(:pairorig)
        if top >= 0
            c = CUR_C[]
            who = get(EMPTIER, (k, (c - 1) - top), "init")
            key2 = (min(top, 4), who)
            CASC[key2] = get(CASC, key2, 0) + 1
        end
    end
end

Core.eval(PG, quote
    function remove_edge!(g :: OwnersGraph, x :: PathNodeId, w :: PathNodeId; rule :: Symbol)
        x == w && return false
        k = edge_key(x, w)
        haskey(g.edges, k) || return false
        delete!(g.edges, k)
        _drop!(g.inc[x], w)
        _drop!(g.inc[w], x)
        REMOVED_BY[rule] = get(REMOVED_BY, rule, 0) + 1
        $(hook)(g, k, rule)
        return true
    end
end)

choice_steps(og) = [k for k in 0:og.nsteps-1 if GraphPath.choice_at(og, k)]
map_nodes(og, k) = sort(unique(x.id for x in get(og.alive, k, SetPathNodesId())), by = n -> n.index)
bump!(s, n = 1) = (TOT[s] = get(TOT, s, 0) + n)

function pinned(g, P)
    g2 = deepcopy(g)
    g2.review_owners = true
    GraphPath.filter!(g2, SetNodesId(P))
    return g2
end

function measure!(e, g)
    bump!(:joins)
    c = e.current_step
    CUR_C[] = c
    kk = c - 2
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    bs = map_nodes(u.og, kk)
    steps = [s for s in choice_steps(u.og) if s != kk]
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(2, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(u.og, s)) for s in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps
        empty!(WATCH)
        h = pinned(u, P)
        h.is_valid || continue
        for b in bs
            side = any(x -> x.id == b, get(e.og.alive, kk, SetPathNodesId())) ? e : g
            empty!(WATCH); empty!(COMMON); empty!(INDEX); empty!(EMPTIER)
            for ed in keys(h.og.edges)
                y, w = ed
                (y.id.step == kk || w.id.step == kk) && continue
                any(r -> r.id == b && PG.has_edge(h.og, w, r), PG.neighbors(h.og, y, kk)) || continue
                WATCH[ed] = kk - max(y.id.step, w.id.step)
            end
            isempty(WATCH) && continue
            watched = collect(keys(WATCH))
            bump!(:watched, length(watched))
            for wk in watched
                x, z = wk
                ix = h.og.inc[x]; iz = h.og.inc[z]
                for (st, sx) in ix
                    (st == x.id.step || st == z.id.step) && continue
                    sz = get(iz, st, nothing)
                    sz === nothing && continue
                    C = Set(cc for cc in sx if cc in sz)
                    COMMON[(wk, st)] = C
                    for cc in C
                        push!(get!(INDEX, PG.edge_key(x, cc), []), (wk, st))
                        push!(get!(INDEX, PG.edge_key(z, cc), []), (wk, st))
                    end
                end
            end
            h2 = pinned(h, [b])
            empty!(WATCH)
            for ed in watched
                alive = h2.is_valid && haskey(h2.og.edges, ed)
                if alive
                    bump!(:good)
                else
                    bump!(:bad)
                    bump!(PG.has_edge(side.og, ed[1], ed[2]) ? :own : :other)
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
        println(io, "instance\tjoins\twatched\tgood\tbad\town\tother\tpairlvl(nivel=n)\tcascada(nivel:quién=n)\tcuts(regla,d)")
        for path in corpus()
            name = basename(path)
            empty!(TALLY); empty!(TOT); empty!(LVL); empty!(CASC)
            try
                machine = SatMachine.new(LOAD(path))
                redirect_stdout(devnull) do
                    SatMachine.run!(machine)
                end
            catch err
                println(io, "$name\tERROR $(typeof(err))"); flush(io); continue
            end
            cuts = join(["$(r):$(d)=$(n)" for ((r, d), n) in sort(collect(TALLY))], " ")
            lvl = join(["$(l)=$(n)" for (l, n) in sort(collect(LVL))], " ")
            casc = join(["$(l):$(w)=$(n)" for ((l, w), n) in sort(collect(CASC))], " ")
            println(io, "$name\t$(get(TOT, :joins, 0))\t$(get(TOT, :watched, 0))\t$(get(TOT, :good, 0))\t$(get(TOT, :bad, 0))\t$(get(TOT, :own, 0))\t$(get(TOT, :other, 0))\t$lvl\t$casc\t$cuts")
            flush(io)
        end
    end
end

main()
