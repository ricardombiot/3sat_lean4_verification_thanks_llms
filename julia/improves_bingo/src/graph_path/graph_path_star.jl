# Regla de la estrella (28-sept-2026; propuesta para PinFree/TopUnion en lean/improves_bingo).
#
# Para cada cima t (nodo vivo del paso current_step - 1), tras el review de siempre: W = t y sus vecinos vivos. Se
# calcula la mayor relación R ⊆ aristas de W (con la diagonal) cerrada por parejas dentro de W: cada pareja (a, b) de
# R tiene, en cada paso l, un w de W con R a w y R b w. S = los y con R t y. Se cortan las aristas t–y con y ∉ S (si
# R t t cae, todas: t muere en la purga). Punto fijo junto con el review.
#
# Solidez: la camarilla de una solución que pasa por t está en W y es cerrada por parejas dentro de sí, así que sus
# parejas quedan en R; solo se cortan aristas que tocan t.
#
# STAR_RULE: :off (por defecto) | :on. Se puede fijar con la variable de entorno STAR_RULE.
const STAR_RULE = Ref(Symbol(get(ENV, "STAR_RULE", "off")))
const STAR_CUT = Ref(0)       # aristas t–y cortadas (solo para medir)
const STAR_KILLED = Ref(0)    # cimas con R t t vacía
const STAR_RUNS = Ref(0)      # pasadas de la regla
const STAR_DROPPED = Ref(0)   # parejas y–z (o diagonales) que salen de R sin tocar t (solo para medir)

# Las y de la estrella de t que se quedan (o nothing si t cae).
function star_keep(og, t :: PathNodeId, c :: Int)
    W = Set{PathNodeId}([t])
    for y in PathOwnersGraph.neighbors_all(og, t)
        push!(W, y)
    end
    R = Dict{PathNodeId, Set{PathNodeId}}(x => Set{PathNodeId}([x]) for x in W)
    for x in W, z in PathOwnersGraph.neighbors_all(og, x)
        z in W && push!(R[x], z)
    end
    byl = Dict{Int, Vector{PathNodeId}}()
    for x in W
        push!(get!(byl, Int(x.id.step), PathNodeId[]), x)
    end
    ok(a, b) = all(l -> any(w -> w in R[a] && w in R[b], get(byl, l, PathNodeId[])), 0:c-1)
    changed = true
    #! [while] $ O(|W|^2) $ vueltas como mucho: cada vuelta que sigue quita al menos una pareja
    while changed
        changed = false
        for a in collect(keys(R)), b in collect(R[a])
            haskey(R, a) && b in R[a] || continue
            (a == b || hash(a) < hash(b)) || continue
            ok(a, b) && continue
            changed = true
            STAR_DROPPED[] += 1
            if a == b
                for z in R[a]; z == a || delete!(R[z], a); end
                delete!(R, a)
                filter!(x -> x != a, byl[Int(a.id.step)])
            else
                delete!(R[a], b); delete!(R[b], a)
            end
        end
    end
    haskey(R, t) || return nothing
    return R[t]
end

function star_rule!(gpath :: GPath) :: Bool
    STAR_RUNS[] += 1
    og = gpath.og
    c = og.nsteps
    tops = collect(get(og.alive, c - 1, SetPathNodesId()))
    cut = false
    for t in tops
        PathOwnersGraph.is_alive(og, t) || continue
        keep = star_keep(og, t, c)
        keep !== nothing || (STAR_KILLED[] += 1)
        for y in collect(PathOwnersGraph.neighbors_all(og, t))
            (y == t || (keep !== nothing && y in keep)) && continue
            PathOwnersGraph.remove_edge!(og, t, y; rule = :star) && (STAR_CUT[] += 1; cut = true)
        end
    end
    if cut
        gpath.review_owners = true
        clean_invalid_nodes!(gpath)
    end
    return cut
end
