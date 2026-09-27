# Argumento global candidato (docs/context/ambfar.md §4.2μ): la red de posesión de un estado como CSP binario (pasos =
# variables, nodos de camino = valores, relación R_{l,l'} = "x posee v"). El review da 3-consistencia fuerte; si las
# relaciones fueran cerradas bajo una mayoría, habría consistencia global (Jeavons–Cohen–Cooper).
# Mayoría natural sobre ventanas: bit a bit sobre (índice del paso, índice del padre, índice del abuelo).
#   DOM: para tres nodos de un paso, el nodo mayoría existe en el estado.
#   MAJ: (x_i, v_i) ∈ R para i = 1..3 (pasos l ≠ l') ⇒ (maj x, maj v) ∈ R (si ambos existen).
# Muestreo: NS ternas por estado. Clasifica los fallos por el tipo de los dos pasos.
#   julia --project=../.. majority_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(53)
const NS = parse(Int, get(ENV, "NS", "2000"))
function tables(g)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table; union!(S, set); end
    end
    U
end
owns(U, r, q) = haskey(U, r) && (q in U[r])
bystep_of(U) = (b = Dict{Int, Vector{PathNodeId}}(); for r in keys(U); push!(get!(b, r.id.step, PathNodeId[]), r); end; b)
bits(x) = (x.id.index, x.parent_id === nothing ? -1 : x.parent_id.index, x.gparent_id === nothing ? -1 : x.gparent_id.index)
maj3(a, b, c) = (a == b || a == c) ? a : b
function majnode(B, xs)
    l = xs[1].id.step
    t = Tuple(map(i -> maj3(bits(xs[1])[i], bits(xs[2])[i], bits(xs[3])[i]), 1:3))
    for y in get(B, l, PathNodeId[])
        bits(y) == t && return y
    end
    nothing
end
function probe(path, st)
    nv = parse(Int, split(first(filter(l -> startswith(l, "p"), readlines(path))))[3])
    kind(l) = l == 0 ? :raiz : l <= 2nv ? :var : l == 2nv + 1 ? :mid : ((l - (2nv + 2)) % 3 == 2 ? :L3 : :L12)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            T = tables(g); B = bystep_of(T)
            steps = [l for l in 0:top if length(get(B, l, PathNodeId[])) >= 2]
            length(steps) >= 2 || return
            for _ in 1:NS
                l = rand(steps); l2 = rand(steps); l == l2 && continue
                prs = [(x, v) for x in B[l] for v in B[l2] if owns(T, x, v)]
                length(prs) >= 3 || continue
                sel = [rand(prs) for _ in 1:3]
                xs = [p[1] for p in sel]; vs = [p[2] for p in sel]
                (length(unique(xs)) == 1 && length(unique(vs)) == 1) && continue
                mx = majnode(B, xs); mv = majnode(B, vs)
                bump(mx === nothing || mv === nothing ? "DOM falla" : "DOM ok")
                (mx === nothing || mv === nothing) && continue
                ok = owns(T, mx, mv)
                tag = "MAJ $(ok ? "ok" : "FALLA") $(kind(min(l, l2)))-$(kind(max(l, l2)))"
                bump(ok ? "MAJ ok" : "MAJ FALLA"); ok || bump(tag)
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
