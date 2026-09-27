# Mecanismo de AFU (lean/improves_bin UnionLine.AFU). U = unión de la línea n, FU = filterAll U S.
# Para c en la cima y m un nodo de mapa que c fija, F_m = filterAll U (S ∪ {m}):
#   STAR:  toda la estrella de c sobrevive: todo x que posee c en FU es nodo de F_m y conserva en F_m cada entrada v
#          de su tabla en FU que también posee c.
#   STARN: al menos los nodos de la estrella sobreviven (sin exigir sus entradas).
#   julia --project=../.. afu_star_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(43)
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}(); P = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
        P[pid_] = Set(node.parents)
    end
    U, P
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function filtG(g, R)
    p = deepcopy(g)
    redirect_stdout(devnull) do; GraphPath.filter!(p, Set(R)); end
    p.is_valid ? p : nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        states = Dict{NodeId, Any}()
        CollectionTimeline.for_each_gpath(m.timeline, top, g -> g.is_valid && (states[g.map_parent_id] = deepcopy(g)))
        if length(states) >= 2
            ks = collect(keys(states))
            U0 = deepcopy(states[ks[1]])
            for k in ks[2:end]
                o = deepcopy(states[k]); o.map_parent_id = U0.map_parent_id
                GraphPath.do_join!(U0, o)
            end
            ids = unique([r.id for r in keys(tables(U0)[1])])
            for S in vcat([NodeId[]], [[x] for x in rand(ids, min(2, length(ids)))])
                FUg = filtG(U0, S); FUg === nothing && continue
                FU, Par = tables(FUg); B = bystep_of(FU); ns = collect(keys(FU))
                cacheX = Dict{NodeId, Any}(); cacheU = Dict{NodeId, Any}()
                Xc(k) = get!(cacheX, k) do
                    haskey(states, k) || return nothing
                    g = filtG(states[k], S); g === nothing ? nothing : (T = tables(g)[1]; (T, bystep_of(T)))
                end
                for c in get(B, top, PathNodeId[])
                    fixed = NodeId[]
                    for l in 0:top-1
                        il = unique([v.id for v in FU[c] if v.id.step == l])
                        length(il) == 1 && push!(fixed, il[1])
                    end
                    star = [x for x in ns if owns(FU, x, c)]
                    for mid in fixed
                        r = get!(cacheU, mid) do
                            g = filtG(U0, vcat(S, [mid])); g === nothing ? nothing : (T = tables(g)[1]; (T, bystep_of(T)))
                        end
                        if r === nothing
                            bump("F_m inválido"); continue
                        end
                        T = r[1]
                        okN = all(x -> haskey(T, x), star)
                        okS = okN && all(x -> all(v -> !owns(FU, v, c) || v in T[x], FU[x]), star)
                        bump(okN ? "STARN ok" : "STARN FALLA")
                        bump(okS ? "STAR ok" : "STAR FALLA")
                        okS || get(st, "ej", 0) >= 4 || (bump("ej"); println("STAR: $(basename(path)) paso $top S=$S c=$c m=$mid"))
                    end
                end
            end
        end
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
