# Sonda de `PieceLocal`: en cada estado de la máquina (unión de piezas en el join), ¿toda clique con testigos
# es clique con testigos dentro de UNA sola pieza?
#
#   julia --project=../.. piecelocal_probe.jl [--k3] f1.cnf ...
#
# Reconstruye las piezas: antes de cada paso, `do_up_filtering!` de cada estado hacia cada hijo (lo mismo que
# `send_to_destine!`); después del paso, cada estado de la línea nueva es la unión de sus piezas.

include("./../../src/main.jl")
key(p) = Alias.as_key(p)

function union_owners(states)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for g in states, (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
function haswit(U, bystep, Q, top)
    for l in 0:top
        any(r -> all(q -> owns(U, r, q), Q), get(bystep, l, PathNodeId[])) || return false
    end
    true
end
function bystep_of(U)
    b = Dict{Int, Vector{PathNodeId}}()
    for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end
    b
end

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
            length(ps) >= 2 || return   # sin join no hay nada que medir
            U = union_owners([g]); B = bystep_of(U)
            Up = [union_owners([p]) for p in ps]; Bp = [bystep_of(u) for u in Up]
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
                bump("Q con testigos en el estado unido (tamaño $(length(Q)))")
                inone = any(i -> isclique(Up[i], Q) && haswit(Up[i], Bp[i], Q, s1), eachindex(Up))
                if inone
                    bump("  en una sola pieza")
                else
                    bump("  NO está en una sola pieza")
                    length(ex) < 8 && push!(ex, "$(basename(path)) paso $s1 clave $(g.map_parent_id) Q=$(map(key, Q))")
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
        println("$(basename(f)): ", join(["$k=$v" for (k, v) in sort(collect(s))], "  "))
    end
    println("── total"); for (k, v) in sort(collect(tot)); println("  $k: $v"); end
    println("── ejemplos"); foreach(println, exs[1:min(end, 10)])
end
main(ARGS)
