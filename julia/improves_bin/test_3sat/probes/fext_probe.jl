# FExt: la versión de mapa de CliqueTri (docs/context/escalera_reader.md §4.2ξ). En los estados de cada línea: si filterAll g R es
# válido (R nodos de mapa de pasos distintos), en cada paso l fuera de R hay un nodo de mapa k con filterAll g (k :: R)
# válido. R vacío y de un nodo exhaustivos; de 2 y 3 nodos, NR al azar por estado entre los R válidos.
#   julia --project=../.. fext_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(parse(Int, get(ENV, "SEED", "83")))
const NR = parse(Int, get(ENV, "NR", "12"))
mapids(g) = (S = Set{NodeId}(); for (_, line) in g.table_lines.table, (pid_, _) in line.table; push!(S, pid_.id); end; collect(S))
function pinned(g, R)
    f = deepcopy(g)
    redirect_stdout(devnull) do
        for r in R; f.is_valid && GraphPath.filter!(f, SetNodesId([r])); end
        if isempty(R); f.review_owners = true; GraphPath.make_review_owners!(f); end
    end
    f
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while true
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            ids = mapids(g)
            bystep = Dict{Int, Vector{NodeId}}()
            for i in ids; push!(get!(bystep, i.step, NodeId[]), i); end
            Rs = Vector{Vector{NodeId}}([NodeId[]]); append!(Rs, [[i] for i in ids])
            for size in 2:3, _ in 1:NR
                R = NodeId[]
                for s in shuffle(collect(keys(bystep)))[1:min(size, length(bystep))]; push!(R, rand(bystep[s])); end
                push!(Rs, R)
            end
            for R in Rs
                f = pinned(g, R)
                f.is_valid || continue
                tag = "|R|=$(length(R))"
                steps = Set(r.step for r in R)
                ok = true
                for l in sort(collect(keys(bystep)))
                    l in steps && continue
                    any(k -> pinned(f, [k]).is_valid, bystep[l]) && continue
                    ok = false
                    get(st, "ej", 0) < 5 && (bump("ej"); println("FExt FALLA $(basename(path)) paso $top R=$R l=$l"))
                    break
                end
                bump("$tag FExt $(ok ? "ok" : "FALLA")")
            end
        end)
        (SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m)) && break
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
