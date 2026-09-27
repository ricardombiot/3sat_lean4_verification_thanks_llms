# Composición de testigos buenos (docs/context/ambfar.md §4.2ν, punto 2). Q clique con testigos de 3 o 4 nodos
# (muestreo NQ por estado y tamaño); corte en cada miembro salvo el de arriba: L = miembros ≤ s. Sufijo τ por los miembros
# ≥ s con nodos por encima de s que poseen Q, y cuyos requisitos que cruzan nombran cada uno un testigo bueno (w posee Q y
# L ∪ {w} es clique con testigos). P = L ∪ {un testigo bueno por requisito}.
#   ∃ELECCIÓN: alguna elección hace de P una clique con testigos.   ∀ELECCIÓN: toda elección (hasta 64 combinaciones).
#   julia --project=../.. compose_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(71)
const NQ = parse(Int, get(ENV, "NQ", "15"))
const K = parse(Int, get(ENV, "K", "8"))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
good(U, B, Q, top) = isclique(U, Q) && all(l -> wit(U, B, Q, l), 0:top)
function randchain(U, B, fixed, top)
    sel = Dict{Int, PathNodeId}()
    function go(l)
        l < 0 && return true
        for c in shuffle(haskey(fixed, l) ? fixed[l] : get(B, l, PathNodeId[]))
            all(p -> owns(U, c, p) && owns(U, p, c), values(sel)) || continue
            sel[l] = c
            go(l - 1) && return true
            delete!(sel, l)
        end
        false
    end
    go(top) ? [sel[l] for l in 0:top] : nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    reqs = Dict{NodeId, Vector{NodeId}}()
    req(id) = get!(reqs, id) do; collect(SatMachine.map_get_node(gmap, id).requires); end
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            U = tables(g); B = bystep_of(U); ns = collect(keys(U))
            for size in (3, 4)
                cnt = 0
                for _ in 1:(40 * NQ)
                    cnt >= NQ && break
                    Q = [rand(ns)]
                    ok = true
                    while length(Q) < size
                        cs = [x for x in ns if all(q -> q.id.step != x.id.step && owns(U, q, x), Q)]
                        isempty(cs) && (ok = false; break)
                        push!(Q, rand(cs))
                    end
                    ok || continue
                    sort!(Q, by = q -> q.id.step)
                    good(U, B, Q, top) || continue
                    cnt += 1
                    wits(t) = [w for w in get(B, t, PathNodeId[]) if all(q -> owns(U, w, q), Q)]
                    for i in 1:size-1
                        s = Q[i].id.step
                        L = Q[1:i]; H = Q[i:end]
                        gw = Dict{Int, Vector{PathNodeId}}()
                        goodw(t) = get!(gw, t) do; [w for w in wits(t) if good(U, B, unique(vcat(L, [w])), top)]; end
                        fx = Dict{Int, Vector{PathNodeId}}(h.id.step => [h] for h in H)
                        for l in s+1:top
                            haskey(fx, l) || (fx[l] = wits(l))
                        end
                        τs = unique([c for c in (randchain(U, B, fx, top) for _ in 1:K) if c !== nothing])
                        for τ in τs
                            crs = unique([r for j in s+1:top for r in req(τ[j+1].id) if 0 <= r.step <= s])
                            opts = [[w for w in goodw(r.step) if w.id == r] for r in crs]
                            any(isempty, opts) && continue   # τ does not satisfy R_gw
                            bump("tamaño $size: τ R_gw")
                            total = prod(length.(opts); init = 1)
                            combos = Iterators.take(Iterators.product(opts...), 64)
                            res = [good(U, B, unique(vcat(L, collect(c))), top) for c in combos]
                            isempty(crs) && (res = [true])
                            if !any(res) && total > 64
                                res = [good(U, B, unique(vcat(L, collect(c))), top) for c in Iterators.product(opts...)]
                                bump("tamaño $size ∃ repetido sin límite ($(total) combinaciones)")
                            end
                            bump("tamaño $size ∃ELECCIÓN $(any(res) ? "ok" : "FALLA")")
                            any(res) || println("∃FALLA $(basename(path)) paso $top tamaño $size corte $i requisitos=$(length(crs)) combinaciones=$total")
                        end
                    end
                end
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
