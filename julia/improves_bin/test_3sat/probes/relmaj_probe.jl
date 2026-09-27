# Versión relativa del argumento de mayoría (docs/context/ambfar.md §4.2μ). P clique con testigos en un estado (1–2
# nodos, muestreo NP por estado). Red restringida N_P: nodos que poseen todo P; R^P_{l,l'} = pares (x, v) de N_P con x
# posee v.
#   MAJ_P: (x_i, v_i) ∈ R^P, i = 1..3 ⇒ maj x, maj v existen, están en N_P y (maj x, maj v) ∈ R^P (NS ternas por P).
#   3C_P:  (x, v) ∈ R^P, paso l ⇒ ∃ r en N_P en l que posee x y v (NS pruebas por P).
# Si ambas valieran, P se extendería a una cadena (Jeavons–Cohen–Cooper relativo a P).
#   julia --project=../.. relmaj_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(59)
const NP = parse(Int, get(ENV, "NP", "20"))
const NS = parse(Int, get(ENV, "NS", "200"))
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
bystep_of(U, nodes) = (b = Dict{Int, Vector{PathNodeId}}(); for r in nodes; push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
wit(U, B, Q, l) = any(r -> all(q -> owns(U, r, q), Q), get(B, l, PathNodeId[]))
bits(x) = (x.id.index, x.parent_id === nothing ? -1 : x.parent_id.index, x.gparent_id === nothing ? -1 : x.gparent_id.index)
maj3(a, b, c) = (a == b || a == c) ? a : b
function majnode(B, xs)
    t = Tuple(map(i -> maj3(bits(xs[1])[i], bits(xs[2])[i], bits(xs[3])[i]), 1:3))
    for y in get(B, xs[1].id.step, PathNodeId[]); bits(y) == t && return y; end
    nothing
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            T = tables(g); ns = collect(keys(T)); B = bystep_of(T, ns)
            Ps = [[x] for x in ns]
            for i in eachindex(ns), k in i+1:length(ns)
                ns[i].id.step != ns[k].id.step && owns(T, ns[i], ns[k]) && push!(Ps, [ns[i], ns[k]])
            end
            shuffle!(Ps)
            cnt = 0
            for P in Ps
                cnt >= NP && break
                (isclique(T, P) && all(l -> wit(T, B, P, l), 0:top)) || continue
                cnt += 1
                NPn = [x for x in ns if all(p -> owns(T, x, p), P)]
                BP = bystep_of(T, NPn)
                steps = [l for l in 0:top if haskey(BP, l)]
                inN = Set(NPn)
                for _ in 1:NS
                    l = rand(steps); l2 = rand(steps); l == l2 && continue
                    prs = [(x, v) for x in BP[l] for v in BP[l2] if owns(T, x, v)]
                    isempty(prs) && continue
                    # 3C_P
                    (x, v) = rand(prs); l3 = rand(steps)
                    bump(any(r -> owns(T, r, x) && owns(T, r, v), BP[l3]) ? "3C_P ok" : "3C_P FALLA")
                    # MAJ_P
                    length(prs) >= 3 || continue
                    sel = [rand(prs) for _ in 1:3]
                    xs = [p[1] for p in sel]; vs = [p[2] for p in sel]
                    (length(unique(xs)) == 1 && length(unique(vs)) == 1) && continue
                    mx = majnode(B, xs); mv = majnode(B, vs)
                    if mx === nothing || mv === nothing
                        bump("MAJ_P DOM falla"); continue
                    end
                    ok = (mx in inN) && (mv in inN) && owns(T, mx, mv)
                    bump(ok ? "MAJ_P ok" : "MAJ_P FALLA")
                    # the same triple in the full network
                    bump(owns(T, mx, mv) ? "(red completa) MAJ ok" : "(red completa) MAJ FALLA")
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
