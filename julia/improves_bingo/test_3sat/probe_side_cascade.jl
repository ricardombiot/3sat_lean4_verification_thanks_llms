# La cascada de las aristas de un solo lado (28-sept-2026; lean/improves_bingo SideLinks.lean, `SideEdges`).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_side_cascade.jl <salida.tsv> [muestras] [semilla]
#
# Como probe_side_cut.jl, y además: para cada arista vigilada (x,z) y cada paso s se guarda al fijar el conjunto de
# entradas comunes C(s) = tabla(x)[s] ∩ tabla(z)[s]; cada arista (x,c) o (z,c) que se quita saca c de C(s), y la que
# lo vacía es «la que vacía» el paso s. Cuando la regla de parejas corta (x,z), para su paso sin entrada común más
# alto se anota quién lo vació: `regla` de la arista que lo vació, con `*` si esa arista era a su vez vigilada (de
# un solo lado: cascada entre ellas), por nivel (0 = cima, 1 = origen, 2 = c-3, ...).
#
# Resumen de probe_side_cut.jl:
#
# En cada join válido (e = el que ya estaba, g = el que llega, U = la unión, c = current_step) y cada nodo del mapa
# b del paso c-2 de un lado S (el otro, O), para P vacío y `muestras` P al azar se fija U en P ++ [b] y se vigilan
# las aristas de U entre dos nodos vivos en S que S no tiene (vienen solo de O). Por cada arista vigilada se anota
# la regla que la quita (pair, parents, sons, clean = muere un extremo, require = el pin mata un extremo) y la
# distancia d = (c-2) - (paso más alto de sus extremos); `left` cuenta las que sobreviven (SidePinned: 0).
# Para las que corta la regla de parejas, `lvl` = pasos en que sus tablas ya no comparten entrada, contados desde la
# cima (0 = c-1, 1 = c-2 el del origen, 2 = c-3, ...): `pairlvl` cuenta por el más alto (el más cercano a la cima)
# y `pairtop`/`pairorig` cuántas fallan (también) en la cima / en el paso del origen.

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

function measure!(e, g)
    bump!(:joins)
    c = e.current_step
    CUR_C[] = c
    u = deepcopy(e)
    PathCollectionLines.union!(u.table_lines, deepcopy(g).table_lines)
    PathOwnersGraph.union!(u.og, deepcopy(g).og)
    steps = [k for k in choice_steps(u.og) if k != c - 2]
    Ps = Vector{Vector{NodeId}}([NodeId[]])
    if !isempty(steps)
        for _ in 1:SAMPLES
            m = rand(RNG[], 1:min(2, length(steps)))
            push!(Ps, [rand(RNG[], map_nodes(u.og, k)) for k in shuffle(RNG[], steps)[1:m]])
        end
    end
    for P in Ps, side in (e, g), b in map_nodes(side.og, c - 2)
        empty!(WATCH)
        for (k, _) in u.og.edges
            x, w = k
            PG.is_alive(side.og, x) && PG.is_alive(side.og, w) && !PG.has_edge(side.og, x, w) || continue
            WATCH[k] = (c - 2) - max(x.id.step, w.id.step)
        end
        isempty(WATCH) && continue
        bump!(:watched, length(WATCH))
        empty!(COMMON); empty!(INDEX); empty!(EMPTIER)
        for wk in keys(WATCH)
            x, z = wk
            ix = u.og.inc[x]; iz = u.og.inc[z]
            for (st, sx) in ix
                (st == x.id.step || st == z.id.step) && continue
                sz = get(iz, st, nothing)
                sz === nothing && continue
                C = Set(c for c in sx if c in sz)
                COMMON[(wk, st)] = C
                for c in C
                    push!(get!(INDEX, PG.edge_key(x, c), []), (wk, st))
                    push!(get!(INDEX, PG.edge_key(z, c), []), (wk, st))
                end
            end
        end
        h = deepcopy(u)
        h.review_owners = true
        GraphPath.filter!(h, SetNodesId(vcat(P, [b])))
        if h.is_valid
            bump!(:left, count(k -> haskey(h.og.edges, k), keys(WATCH)))
        else
            bump!(:deadpin, length(WATCH))   # el pin mata la unión: lo que quede vigilado cae con ella
        end
        empty!(WATCH)
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
        println(io, "instance\tjoins\twatched\tleft\tdeadpin\tpairtop\tpairorig\tpairlvl(nivel=n)\tcascada(nivel:quién=n)\tcuts(regla,d)")
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
            println(io, "$name\t$(get(TOT, :joins, 0))\t$(get(TOT, :watched, 0))\t$(get(TOT, :left, 0))\t$(get(TOT, :deadpin, 0))\t$(get(TOT, :pairtop, 0))\t$(get(TOT, :pairorig, 0))\t$lvl\t$casc\t$cuts")
            flush(io)
        end
    end
end

main()
