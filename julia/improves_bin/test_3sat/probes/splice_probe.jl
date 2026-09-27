# Empalme de certificados (docs/context/ambfar.md §4.2μ). En cada estado se toman hasta NC cadenas (búsqueda aleatoria).
# Para dos cadenas σ, τ que comparten el nodo del paso s, el empalme σ[≤ s] ++ τ[> s] respeta las ventanas (un nodo es una
# ventana). SPL: ¿es una cadena del estado (todos sus nodos se poseen)? Si no, REQ: ¿hay un nodo del sufijo cuyo requisito
# nombra un paso del prefijo con un nodo de otro valor? (el requisito de largo alcance que rompe el empalme).
#   julia --project=../.. splice_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(61)
const NC = parse(Int, get(ENV, "NC", "40"))
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
function randchain(U, B, top)
    sel = Dict{Int, PathNodeId}()
    function go(l)
        l < 0 && return true
        for c in shuffle(get(B, l, PathNodeId[]))
            all(p -> owns(U, c, p) && owns(U, p, c), values(sel)) || continue
            sel[l] = c
            go(l - 1) && return true
            delete!(sel, l)
        end
        false
    end
    go(top) ? [sel[l] for l in 0:top] : nothing
end
ischain(U, ch) = all(i -> all(j -> owns(U, ch[i], ch[j]), eachindex(ch)), eachindex(ch))
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            U = tables(g); B = bystep_of(U)
            chs = unique([c for c in (randchain(U, B, top) for _ in 1:NC) if c !== nothing])
            for a in eachindex(chs), b in eachindex(chs)
                a == b && continue
                σ, τ = chs[a], chs[b]
                for s in 1:top-1
                    σ[s+1] == τ[s+1] || continue
                    (σ[s] != τ[s] || σ[s+2] != τ[s+2]) || continue
                    sp = vcat(σ[1:s+1], τ[s+2:end])
                    ok = ischain(U, sp)
                    bump(ok ? "SPL ok" : "SPL FALLA")
                    if !ok
                        req = false
                        for j in s+2:top+1
                            dn = SatMachine.map_get_node(gmap, sp[j].id)
                            for r in dn.requires
                                r.step + 1 <= s + 1 && sp[r.step+1].id != r && (req = true)
                            end
                        end
                        bump(req ? "SPL FALLA con requisito violado" : "SPL FALLA sin requisito violado")
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
