# Dos vías para PieceLocal (lean/improves_bin, PieceJoin.lean), medidas en cada estado unido (≥ 2 piezas):
#   A (crecer): para Q clique con testigos y cada paso l sin miembro, ¿hay x en l con x::Q clique con testigos?
#   B (clave): ¿hay testigos frontera r (paso n) y w (paso n+1) de Q con w ∋ r? ¿Q ∪ {r, w} sigue siendo clique con
#      testigos? ¿la pieza de w es buena (Q clique con testigos dentro)?
#   julia --project=../.. join_grow_probe.jl [--k3] f1.cnf ...
include("./../../src/main.jl")
key(p) = Alias.as_key(p)
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
haswit(U, B, Q, top) = all(l -> wit(U, B, Q, l), 0:top)
function probe(path; k3 = false)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    ncl = length(filter(l -> !isempty(l) && !(l[1] in ('c', 'p', '%')), readlines(path)))
    kindof(l, s1) = l == 0 ? "raíz" : l <= 2nv ? "var" : l == 2nv + 1 ? "mid" : l == s1 ? "nuevo" :
        l < 2nv + 2 + 3ncl ? "L$((l - (2nv + 2)) % 3 + 1)" : "fin"
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    st = Dict{String, Int}(); bump(k) = (st[k] = get(st, k, 0) + 1)
    ex = String[]
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid && push!(get!(pieces, d, Any[]), p)
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            U = tables(g); B = bystep_of(U)
            Up = [tables(p) for p in ps]; Bp = [bystep_of(u) for u in Up]
            nodes = collect(keys(U))
            Qs = [[x] for x in nodes]
            for i in eachindex(nodes), k in i+1:length(nodes)
                nodes[i].id.step == nodes[k].id.step && continue
                push!(Qs, [nodes[i], nodes[k]])
            end
            if k3
                vn = [x for x in nodes if 1 <= x.id.step <= 2nv]
                for i in eachindex(vn), k in i+1:length(vn), j in k+1:length(vn)
                    length(Set([vn[i].id.step, vn[k].id.step, vn[j].id.step])) == 3 || continue
                    push!(Qs, [vn[i], vn[k], vn[j]])
                end
            end
            for Q in Qs
                (isclique(U, Q) && haswit(U, B, Q, s1)) || continue
                bump("Q con testigos")
                # A: crecer en cada paso sin miembro
                for l in 0:s1
                    any(q -> q.id.step == l, Q) && continue
                    ok = any(x -> isclique(U, vcat([x], Q)) && haswit(U, B, vcat([x], Q), s1), get(B, l, PathNodeId[]))
                    bump(ok ? "A ok: crece" : "A FALLA en paso $(kindof(l, s1))")
                    if !ok && length(ex) < 10
                        push!(ex, "A $(basename(path)) paso $s1 Q=$(map(key, Q)) no crece en $l ($(kindof(l, s1)))")
                    end
                end
                # B: testigos frontera compatibles
                ws = [w for w in get(B, s1, PathNodeId[]) if all(q -> owns(U, w, q), Q)]
                rs = [r for r in get(B, s1 - 1, PathNodeId[]) if all(q -> owns(U, r, q), Q)]
                pairs = [(r, w) for r in rs for w in ws if owns(U, w, r)]
                bump(isempty(pairs) ? "B1 FALLA: ningún par frontera compatible" : "B1 ok: hay par frontera compatible")
                isempty(pairs) && continue
                grows = [(r, w) for (r, w) in pairs if isclique(U, vcat([r, w], Q)) && haswit(U, B, vcat([r, w], Q), s1)]
                bump(isempty(grows) ? "B2 FALLA: ningún par crece" : "B2 ok: algún par frontera crece Q")
                bump(length(grows) == length(pairs) ? "B2' ok: todo par frontera crece Q" : "B2' FALLA: algún par no crece")
                pieceof(w) = findfirst(i -> haskey(Up[i], w), eachindex(Up))
                good(i) = i !== nothing && isclique(Up[i], Q) && haswit(Up[i], Bp[i], Q, s1)
                if !isempty(grows)
                    bump(all(((r, w),) -> good(pieceof(w)), grows) ? "B3 ok: la pieza de todo par que crece es buena" :
                         "B3 FALLA: pieza de un par que crece no es buena")
                end
            end
        end)
    end
    st, ex
end
function main(args)
    k3 = "--k3" in args
    files = filter(a -> !startswith(a, "--"), args)
    tot = Dict{String, Int}(); exs = String[]
    for f in files
        s, e = try probe(f; k3 = k3) catch err; println("$(basename(f)): SALTADA ($(typeof(err)))"); continue end
        for (k, v) in s; tot[k] = get(tot, k, 0) + v; end
        append!(exs, e)
    end
    println("── total"); for (k, v) in sort(collect(tot)); println("  $k: $v"); end
    println("── ejemplos"); foreach(println, exs[1:min(end, 10)])
end
main(ARGS)
