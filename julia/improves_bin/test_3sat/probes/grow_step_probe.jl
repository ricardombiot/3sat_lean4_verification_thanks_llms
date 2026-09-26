# Vía 1, crecimiento paso a paso (lean/improves_bin, PieceLocal por inducción).
# Para cada clique Q con testigos de un estado G de la máquina y cada paso t sin miembro de Q:
#   X1 (débil): ∃ r en el paso t con Q ∪ {r} clique con testigos en G.
#   X2 (fuerte): todo testigo r de Q en el paso t cumple que Q ∪ {r} es clique con testigos.
#   X3 (voraz): completar Q paso a paso (de arriba abajo) eligiendo cualquier r válido nunca se atasca
#       y termina en una clique con un nodo por paso.
# En los estados unidos, además:
#   X4: Q buena en la pieza P ⇒ la extensión r puede tomarse en P con Q ∪ {r} buena en P.
#   julia --project=../.. grow_step_probe.jl [--k3] f1.cnf ...
include("./../../src/main.jl")
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
function bystep_of(U)
    b = Dict{Int, Vector{PathNodeId}}()
    for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end
    b
end
haswit(U, B, Q, top) = all(l -> any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[])), 0:top)
good(U, B, Q, top) = isclique(U, Q) && haswit(U, B, Q, top)
wits(U, B, Q, t) = [r for r in get(B, t, PathNodeId[]) if all(q -> owns(U, r, q), Q)]
function greedy(U, B, Q, top)
    Q = copy(Q)
    for t in top:-1:0
        any(q -> q.id.step == t, Q) && continue
        c = [r for r in wits(U, B, Q, t) if good(U, B, vcat(Q, [r]), top)]
        isempty(c) && return false
        push!(Q, c[1])
    end
    true
end

function probe(path; k3 = false)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    st = Dict{String, Int}(); bump(k) = (st[k] = get(st, k, 0) + 1)
    while true
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
        (SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m)) && break
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            joined = length(ps) >= 2
            tag = joined ? "unido" : "simple"
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
                good(U, B, Q, s1) || continue
                bump("$tag Q con testigos")
                bump(greedy(U, B, Q, s1) ? "$tag X3 ok: voraz completa" : "$tag X3 FALLA: voraz se atasca")
                gi = joined ? [i for i in eachindex(Up) if good(Up[i], Bp[i], Q, s1)] : Int[]
                for t in 0:s1
                    any(q -> q.id.step == t, Q) && continue
                    W = wits(U, B, Q, t)
                    ext = [r for r in W if good(U, B, vcat(Q, [r]), s1)]
                    bump(!isempty(ext) ? "$tag X1 ok" : "$tag X1 FALLA")
                    bump(length(ext) == length(W) ? "$tag X2 ok" : "$tag X2 FALLA: testigo que no extiende")
                    if joined
                        x4 = any(i -> any(r -> good(Up[i], Bp[i], vcat(Q, [r]), s1), wits(Up[i], Bp[i], Q, t)), gi)
                        bump(x4 ? "$tag X4 ok" : "$tag X4 FALLA")
                    end
                end
            end
        end)
    end
    st
end

function main(args)
    k3 = "--k3" in args
    tot = Dict{String, Int}()
    for f in filter(a -> !startswith(a, "--"), args)
        s = try probe(f; k3 = k3) catch err; println("$(basename(f)): SALTADA ($err)"); continue end
        for (k, v) in s; tot[k] = get(tot, k, 0) + v; end
    end
    println("── total"); for (k, v) in sort(collect(tot)); println("  $k: $v"); end
end
main(ARGS)
