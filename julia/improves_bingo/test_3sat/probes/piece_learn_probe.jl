# Sonda para aprender a formalizar `PieceLocal` (lean/improves_bin, PieceJoin.lean).
#
#   julia --project=../.. piece_learn_probe.jl [--k3] f1.cnf ...
#
# En cada join (estado con ≥ 2 piezas), mide hipótesis candidatas a lema:
#   E1 (entrada local): si r y q son nodos de una pieza P y r posee q en el estado unido, r posee q en P.
#   E0 (nodos): todo nodo del estado unido es nodo de alguna pieza (trivial, control).
# y para cada clique Q con testigos del estado unido, con w un testigo del paso nuevo y P_w su pieza:
#   E2: todo miembro de Q es nodo de P_w.
#   E3: en cada paso hay un testigo del estado unido que es nodo de P_w.
#   E4: Q es clique con testigos dentro de P_w (lo que pediría PieceLocal eligiendo la pieza de w).
# Si E1, E2 y E3 valen siempre, PieceLocal sale de ellas: el testigo nodo de P_w posee Q en el unido, y por E1
# también en P_w.

include("./../../src/main.jl")
key(p) = Alias.as_key(p)

function tables(states)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for g in states, (_, line) in g.table_lines.table, (pid_, node) in line.table
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

function probe(path; k3 = false)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
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
            U = tables([g]); B = bystep_of(U)
            Up = [tables([p]) for p in ps]; Bp = [bystep_of(u) for u in Up]
            # E1rw: entrada entre dos nodos poseídos (en P) por un par frontera compatible (r en n, w en n+1, w ∋ r)
            for i in eachindex(Up)
                for w in get(Bp[i], s1, PathNodeId[]), r in get(Bp[i], s1 - 1, PathNodeId[])
                    owns(Up[i], w, r) || continue
                    T = [q for q in Up[i][w] if haskey(Up[i], q) && q.id.step < s1 - 1 && owns(Up[i], r, q)]
                    for a in T, b in T
                        owns(U, a, b) || continue
                        bump(owns(Up[i], a, b) ? "E1rw ok" : "E1rw FALLA")
                    end
                end
            end
            # E1w: entrada entre dos nodos poseídos (en P) por un mismo nodo del paso nuevo de P
            for i in eachindex(Up)
                for w in get(Bp[i], s1, PathNodeId[])
                    T = [q for q in Up[i][w] if haskey(Up[i], q) && q.id.step < s1]
                    for r in T, q in T
                        owns(U, r, q) || continue
                        bump(owns(Up[i], r, q) ? "E1w ok" : "E1w FALLA")
                    end
                end
            end
            # E0 y E1 sobre todas las entradas
            for (r, S) in U
                inP = [i for i in eachindex(Up) if haskey(Up[i], r)]
                bump(isempty(inP) ? "E0 FALLA: nodo en ninguna pieza" : "E0 ok")
                for q in S, i in inP
                    haskey(Up[i], q) || continue
                    if q in Up[i][r]
                        bump("E1 ok")
                    else
                        bump("E1 FALLA: r,q nodos de P, r posee q en el unido pero no en P")
                        length(ex) < 0 && push!(ex, "E1 $(basename(path)) paso $s1 r=$(key(r)) q=$(key(q))")
                    end
                end
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
            for Q in Qs, i in eachindex(Up)
                isclique(Up[i], Q) || continue
                bump(haswit(Up[i], Bp[i], Q, s1) ? "H6' ok: clique en P ⇒ testigos en P (sin condición)" :
                     (haswit(U, B, Q, s1) ? "H6' FALLA con testigos en el unido" : "H6' FALLA sin testigos en el unido"))
            end
            for Q in Qs
                (isclique(U, Q) && haswit(U, B, Q, s1)) || continue
                bump("Q con testigos")
                tops = [w for w in get(B, s1, PathNodeId[]) if all(q -> owns(U, w, q), Q)]
                good = [i for i in eachindex(Up) if isclique(Up[i], Q) && haswit(Up[i], Bp[i], Q, s1)]
                cliq = [i for i in eachindex(Up) if isclique(Up[i], Q)]
                topP = unique([i for w in tops for i in eachindex(Up) if haskey(Up[i], w) && all(q -> owns(Up[i], w, q), Q)])
                bump(isempty(good) ? "  PieceLocal FALLA" : "  PieceLocal ok")
                bump(isempty(cliq) ? "  H9 FALLA: en ninguna pieza es clique" : "  H9 ok: es clique en alguna pieza")
                bump(Set(good) == Set(cliq) ? "  H6 ok: clique en P ⇒ testigos en P" : "  H6 FALLA: clique en P sin testigos en P")
                bump(Set(good) == Set(topP) ? "  H7 ok: buena ⇔ contiene un top que posee Q en P" : "  H7 FALLA")
                bump(issubset(Set(topP), Set(good)) ? "  H8 ok: top que posee Q en P ⇒ buena" : "  H8 FALLA")
                ct = intersect(cliq, topP)
                # frontera: testigos del paso anterior (s1-1) y del nuevo (s1), y en qué piezas son nodos
                mids = [r for r in get(B, s1 - 1, PathNodeId[]) if all(q -> owns(U, r, q), Q)]
                pw = unique([i for w in tops for i in eachindex(Up) if haskey(Up[i], w)])
                pr = unique([i for r in mids for i in eachindex(Up) if haskey(Up[i], r)])
                both = intersect(pw, pr)
                bump(isempty(both) ? "  H13: ninguna pieza tiene ambos testigos frontera" : "  H13: alguna pieza tiene ambos")
                if !isempty(both)
                    bump(issubset(Set(both), Set(good)) ? "  H13 ok: pieza con ambos testigos frontera ⇒ buena" : "  H13 FALLA")
                    bump(!isempty(intersect(both, good)) ? "  H14 ok: alguna pieza con ambos es buena" : "  H14 FALLA")
                end
                bump(all(r -> count(i -> haskey(Up[i], r), eachindex(Up)) == 1, mids) ? "  H15 ok: testigo frontera n en una sola pieza" : "  H15 FALLA")
                bump(Set(good) == Set(ct) ? "  H10 ok: buena ⇔ clique en P y top que posee Q en P" : "  H10 FALLA")
                # H11: pieza donde Q es clique Y cada miembro posee, en P, a un top que posee Q en P
                cw = [i for i in cliq if any(w -> haskey(Up[i], w) && all(q -> owns(Up[i], w, q) && owns(Up[i], q, w), Q), get(B, s1, PathNodeId[]))]
                bump(Set(good) == Set(cw) ? "  H11 ok" : "  H11 FALLA")
                bump(issubset(Set(good), Set(ct)) ? "  H12 ok: buena ⇒ clique y top en P" : "  H12 FALLA")
                kindof(l) = l == 0 ? "raíz" : l <= 2nv ? "var" : l == 2nv + 1 ? "mid" : l == s1 ? "nuevo" : "L$((l - (2nv + 2)) % 3 + 1)"
                for i in cliq
                    misses = [l for l in 0:s1 if !any(r -> all(q -> owns(Up[i], r, q), Q), get(Bp[i], l, PathNodeId[]))]
                    ks = Set(kindof(l) for l in misses)
                    bump("  H18 pieza-clique: pasos sin testigo = $(isempty(ks) ? "ninguno" : join(sort(collect(ks)), "+"))")
                end
                # H19: la pieza buena, ¿es la única que tiene testigo en todos los L3 anteriores?
                l3s = [l for l in 0:s1-1 if kindof(l) == "L3"]
                allL3 = [i for i in cliq if all(l -> any(r -> all(q -> owns(Up[i], r, q), Q), get(Bp[i], l, PathNodeId[])), l3s)]
                bump(Set(allL3) == Set(good) ? "  H19 ok: buena ⇔ clique con testigos en todos los L3" : "  H19 FALLA")
                for i in setdiff(cliq, good)
                    miss = first(l for l in 0:s1 if !any(r -> all(q -> owns(Up[i], r, q), Q), get(Bp[i], l, PathNodeId[])))
                    kind = miss == 0 ? "raíz" : miss <= 2nv ? "var" : miss == 2nv + 1 ? "mid" : "L$((miss - (2nv + 2)) % 3 + 1)"
                    bump("  H6 falla: falta testigo en paso de tipo $kind ($(miss == s1 ? "paso nuevo" : "inferior"))")
                    length(ex) < 40 && push!(ex, "H6 $(basename(path)) paso $s1 Q=$(map(key, Q)) pieza=$i falta=$miss ($kind) buenas=$good")
                end
                for w in tops
                    iw = [i for i in eachindex(Up) if haskey(Up[i], w)]
                    length(iw) == 1 || (bump("  top en $(length(iw)) piezas"); continue)
                    i = iw[1]
                    bump(isclique(Up[i], Q) ? "  H16 ok: Q es clique en la pieza de cada top w" : "  H16 FALLA")
                    e2 = all(q -> haskey(Up[i], q), Q)
                    bump(e2 ? "  E2 ok" : "  E2 FALLA: miembro fuera de P_w")
                    e3 = all(l -> any(r -> haskey(Up[i], r) && all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[])), 0:s1)
                    bump(e3 ? "  E3 ok" : "  E3 FALLA: algún paso sin testigo nodo de P_w")
                    e4 = isclique(Up[i], Q) && haswit(Up[i], Bp[i], Q, s1)
                    bump(e4 ? "  E4 ok" : "  E4 FALLA: Q no es clique con testigos en P_w")
                    if !e4 && length(ex) < 0
                        push!(ex, "E4 $(basename(path)) paso $s1 Q=$(map(key, Q)) w=$(key(w)) E2=$e2 E3=$e3")
                    end
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
        println("$(basename(f)) listo")
    end
    println("── total"); for (k, v) in sort(collect(tot)); println("  $k: $v"); end
    println("── ejemplos"); foreach(println, exs[1:min(end, 12)])
end
main(ARGS)
