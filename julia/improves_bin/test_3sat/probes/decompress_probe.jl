# Vía "compresión sin pérdida" del join (lean/improves_bin, PieceJoin.PieceLocal).
# El join es unión pura (sin review). ¿Se recupera cada pieza filtrando el estado unido por la clave de su fuente?
#   D1: tablas de filter(J, {k_i}) == tablas de P_i        (descompresión exacta)
#   D1s: filter(J, {k_i}) ⊆ P_i  (entrada a entrada)       D1c: P_i ⊆ filter(J, {k_i})
#   SYM: la posesión es simétrica en J
# y para cada clique Q con testigos de J:
#   F1: pieza buena i ⇔ Q clique con testigos en filter(J, {k_i})
#   F3: alguna i con testigo de paso n en P_i tiene Q clique con testigos en filter(J,{k_i})
#   julia --project=../.. decompress_probe.jl [--k3] f1.cnf ...
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
good(U, Q, top) = isclique(U, Q) && haswit(U, bystep_of(U), Q, top)
sub(U, V) = all(((r, S),) -> haskey(V, r) && issubset(S, V[r]), U)

function probe(path; k3 = false)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    st = Dict{String, Int}(); bump(k) = (st[k] = get(st, k, 0) + 1)
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
                p.is_valid && push!(get!(pieces, d, Any[]), (g.map_parent_id, p))
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        s1 = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s1, function (g)
            ps = get(pieces, g.map_parent_id, Any[])
            length(ps) >= 2 || return
            bump("joins")
            U = tables(g)
            bump(all(((r, S),) -> all(q -> !haskey(U, q) || owns(U, q, r), S), U) ? "SYM ok" : "SYM FALLA")
            Up = [tables(p) for (_, p) in ps]
            Uf = map(ps) do (k, _)
                f = deepcopy(g)
                redirect_stdout(devnull) do; GraphPath.filter!(f, Set([k])); end
                f.is_valid ? tables(f) : Dict{PathNodeId, Set{PathNodeId}}()
            end
            for i in eachindex(Up)
                a = sub(Uf[i], Up[i]); b = sub(Up[i], Uf[i])
                bump(a && b ? "D1 ok: filtrar por la clave recupera la pieza" : "D1 FALLA")
                bump(a ? "D1s ok" : "D1s FALLA: filtro con entrada ajena a la pieza")
                bump(b ? "D1c ok" : "D1c FALLA: filtro pierde entrada de la pieza")
            end
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
                good(U, Q, s1) || continue
                bump("Q con testigos")
                gi = [i for i in eachindex(Up) if good(Up[i], Q, s1)]
                fi = [i for i in eachindex(Uf) if good(Uf[i], Q, s1)]
                bump(Set(gi) == Set(fi) ? "  F1 ok: buena ⇔ buena tras filtrar J por su clave" : "  F1 FALLA")
                bump(!isempty(fi) ? "  F2 ok: alguna descompresión la conserva" : "  F2 FALLA")
                wn = [i for i in eachindex(Up) if any(r -> r.id.step == s1 - 1 && all(q -> owns(U, r, q), Q), keys(Up[i]))]
                bump(all(i -> good(Uf[i], Q, s1), wn) ? "  F3 ok: toda pieza con testigo en n la conserva al filtrar" : "  F3 FALLA")
                # H20: alguna clave k_i de paso n es co-poseída por testigos en todos los pasos (WitR J Q [k_i])
                B = bystep_of(U)
                wk(k) = all(l -> any(r -> all(q -> owns(U, r, q), Q) && any(v -> v.id == k, U[r]), get(B, l, PathNodeId[])), 0:s1)
                hi = [i for i in eachindex(ps) if wk(ps[i][1])]
                bump(!isempty(hi) ? "  H20 ok: ∃ k_i con WitR J Q [k_i]" : "  H20 FALLA")
                bump(Set(hi) == Set(gi) ? "  H21 ok: buena ⇔ WitR J Q [k_i]" : "  H21 FALLA")
                bump(issubset(Set(hi), Set(fi)) ? "  FP ok: WitR J Q [k_i] ⇒ sobrevive al filtro por k_i" : "  FP FALLA")
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
