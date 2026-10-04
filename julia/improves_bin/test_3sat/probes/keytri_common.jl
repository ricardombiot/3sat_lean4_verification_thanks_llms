# Común a keytri_probe.jl y m1aall_probe.jl: estados unidos J de cada línea, fijados en R (pins con su review).
include("./../../src/main.jl")
using Random
Random.seed!(parse(Int, get(ENV, "SEED", "97")))
const NR = parse(Int, get(ENV, "NR", "10"))
mapids(g) = (S = Set{NodeId}(); for (_, line) in g.table_lines.table, (pid_, _) in line.table; push!(S, pid_.id); end; collect(S))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
function pinned(g, R)
    f = deepcopy(g)
    redirect_stdout(devnull) do
        f.review_owners = true; GraphPath.make_review_owners!(f)
        for r in R; f.is_valid && GraphPath.filter!(f, SetNodesId([r])); end
    end
    f
end
function sampleR(g)
    ids = mapids(g); bystep = Dict{Int, Vector{NodeId}}()
    for i in ids; push!(get!(bystep, i.step, NodeId[]), i); end
    Rs = Vector{Vector{NodeId}}([NodeId[]]); append!(Rs, [[i] for i in ids])
    for size in 2:3, _ in 1:NR
        ks = shuffle(collect(keys(bystep)))[1:min(size, length(bystep))]
        push!(Rs, [rand(bystep[s]) for s in ks])
    end
    Rs
end
# f(path, J, top): para cada estado unido válido de cada línea (cima `top`, claves en top-1).
function for_each_join(f, path)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        top >= 2 || continue
        CollectionTimeline.for_each_gpath(m.timeline, top, J -> (J.is_valid && f(J, top)))
    end
end
function run_all(probe)
    st = Dict{String, Int}()
    for f in ARGS
        t = time()
        try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
        println("$(basename(f)): $(round(time() - t; digits = 1)) s"); flush(stdout)
    end
    for (k, v) in sort(collect(st)); println("  $k: $v"); end
end
