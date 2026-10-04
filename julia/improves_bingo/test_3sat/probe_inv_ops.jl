# StarCore como invariante de la máquina, operación por operación (28-sept-2026; StarCore.lean).
#
#   PROBE_MAP=bin julia --project=. test_3sat/probe_inv_ops.jl <salida.tsv> [muestras] [semilla]
#
# Inv0(h): toda cima viva t de h (paso nsteps-1) está en el núcleo por parejas de su estrella (R t t) y ese núcleo
# cumple enlaces a padre/hijo y node (docs de h). InvQ(h): Inv0 de h fijado en P vacío y `muestras` P.
# Por operación (estados de la máquina), con la entrada y la salida:
#   pr (filter_require sin review), pin (filter!: requisitos + review), up (do_up!: fila nueva + review),
#   jr (join: unión sin review), jv (la unión revisada)
#   <op>_n: aplicaciones; <op>_in: entradas con Inv0 falso; <op>_out: salidas con Inv0 falso;
#   <op>_brk: entrada con Inv0 y salida sin; <op>_keep / <op>_links: cimas que fallan por R t t / por enlaces
#   upQ / jvQ: salidas con InvQ falso (fijadas en P vacío y `muestras` P)

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

function star_core(og, t, c)
    W = Set{PathNodeId}([t]); foreach(y -> push!(W, y), PG.neighbors_all(og, t))
    R = Dict{PathNodeId, Set{PathNodeId}}(x => Set{PathNodeId}([x]) for x in W)
    ne = 0
    for x in W, z in PG.neighbors_all(og, x)
        z in W && (push!(R[x], z); ne += 1)
    end
    byl = Dict{Int, Vector{PathNodeId}}()
    for x in W; push!(get!(byl, Int(x.id.step), PathNodeId[]), x); end
    ok(a, b) = all(l -> any(w -> w in R[a] && w in R[b], get(byl, l, PathNodeId[])), 0:c-1)
    changed = true
    while changed
        changed = false
        for a in collect(keys(R)), b in collect(R[a])
            haskey(R, a) && b in R[a] || continue
            (a == b || hash(a) < hash(b)) || continue
            ok(a, b) && continue
            changed = true
            if a == b
                for z in R[a]; z == a || delete!(R[z], a); end
                delete!(R, a); filter!(x -> x != a, byl[Int(a.id.step)])
            else
                delete!(R[a], b); delete!(R[b], a)
            end
        end
    end
    return W, R, ne ÷ 2
end


function inv0(h)
    (h.is_valid && h.og.valid) || return (0, 0)
    og = h.og; c = og.nsteps
    getn(x) = PathCollectionLines.get_node(h.table_lines, x)
    keep = 0; links = 0
    for t in collect(get(og.alive, c - 1, SetPathNodesId()))
        W, R, _ = star_core(og, t, c)
        haskey(R, t) || (keep += 1; continue)
        Rr(x, z) = haskey(R, x) && z in R[x]
        bad = false
        for x in keys(R)
            n = getn(x)
            n === nothing && (bad = true; break)
            if (x.parent_id !== nothing && !any(p -> Rr(x, p), n.parents)) ||
               (x.id.step != c - 1 && !any(s -> Rr(x, s), n.sons))
                bad = true; break
            end
            for w in R[x]
                w == x && continue
                if (x.id.step >= 1 && !any(p -> Rr(x, p) && Rr(p, w), n.parents)) ||
                   (x.id.step + 1 < c && !any(s -> Rr(x, s) && Rr(s, w), n.sons))
                    bad = true; break
                end
            end
            bad && break
        end
        bad && (links += 1)
    end
    return (keep, links)
end
okinv(r) = r == (0, 0)

function record!(op, rin, rout)
    bump!(Symbol(op, "_n"))
    okinv(rin) || bump!(Symbol(op, "_in"))
    okinv(rout) || bump!(Symbol(op, "_out"))
    okinv(rin) && !okinv(rout) && bump!(Symbol(op, "_brk"))
    bump!(Symbol(op, "_keep"), rout[1]); bump!(Symbol(op, "_links"), rout[2])
end

function invQ_bad(h)
    h.is_valid || return false
    for P in samplesP(h)
        okinv(inv0(pinned(h, P))) || return true
    end
    return false
end

function reviewed(g)
    g2 = deepcopy(g); g2.is_valid = g2.og.valid; g2.review_owners = true
    GraphPath.make_review_owners!(g2)
    return g2
end

Core.eval(GraphPath, quote
    function do_join!(gpath :: GPath, gpath_inmutable :: GPath)
        if is_valid_join(gpath, gpath_inmutable)
            a = $(inv0)(gpath); b = $(inv0)(gpath_inmutable)
            rin = (a[1] + b[1], a[2] + b[2])
            gpath_inmutable = deepcopy(gpath_inmutable)
            PathCollectionLines.union!(gpath.table_lines, gpath_inmutable.table_lines)
            PathOwnersGraph.union!(gpath.og, gpath_inmutable.og)
            $(record!)(:jr, rin, $(inv0)(gpath))
            rv = $(reviewed)(gpath)
            $(record!)(:jv, rin, $(inv0)(rv))
            $(invQ_bad)(rv) && $(bump!)(:jvQ)
        end
    end
    function do_up_filtering!(gpath :: GPath, requires :: SetNodesId, map_id_node :: NodeId, title :: String,
                              prohibited :: Set{PathNodeId} = Set{PathNodeId}())
        r0 = $(inv0)(gpath)
        for b in requires
            filter_require!(gpath, b)
        end
        $(record!)(:pr, r0, $(inv0)(gpath))
        make_review_owners!(gpath)
        r1 = $(inv0)(gpath)
        $(record!)(:pin, r0, r1)
        do_up!(gpath, map_id_node, title, prohibited)
        $(record!)(:up, r1, $(inv0)(gpath))
        gpath.is_valid && $(invQ_bad)(gpath) && $(bump!)(:upQ)
    end
end)

const COLS = (Tuple(Symbol(o, '_', k) for o in ("pr", "pin", "up", "jr", "jv") for k in ("n", "in", "out", "brk", "keep", "links"))..., :upQ, :jvQ)

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
