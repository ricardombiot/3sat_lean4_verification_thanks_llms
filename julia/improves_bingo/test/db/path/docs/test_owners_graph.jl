# F1 del plan docs/plans/graph_owners.md: el grafo de owners solo, sin GPath.
using Random

const OG = PathOwnersGraph
const PId = Main.AbsSat.Alias.PathNodeId

og_id(step, index) = PId(nothing, nothing, (step = step, index = index))

function og_with_steps(n)
    g = OG.new()
    for _ in 1:n
        OG.add_step!(g)
    end
    return g
end

@testset "OwnersGraph: aristas simétricas, una vez" begin
    g = og_with_steps(2)
    x, w = og_id(0, 0), og_id(1, 0)
    OG.register!(g, x); OG.register!(g, w)

    @test OG.has_edge(g, x, x)                 # reflexiva implícita
    @test !OG.has_edge(g, x, w)
    e = OG.add_edge!(g, w, x)
    @test (e.a, e.b) == (x, w)                 # clave ordenada, sea cual sea el orden de llamada
    @test OG.add_edge!(g, x, w) === e          # la misma arista, no otra
    @test length(g.edges) == 1
    @test OG.has_edge(g, x, w) && OG.has_edge(g, w, x)
    @test w in OG.neighbors(g, x, 1) && x in OG.neighbors(g, w, 0)
    @test OG.other(e, x) == w && OG.other(e, w) == x
    @test OG.add_edge!(g, x, x) === nothing    # la reflexiva no tiene objeto
    @test OG.check_invariants(g)
end

@testset "OwnersGraph: remove_edge! y validez" begin
    g = og_with_steps(2)
    x, w = og_id(0, 0), og_id(1, 0)
    OG.register!(g, x); OG.register!(g, w)
    OG.add_edge!(g, x, w)
    @test OG.is_valid_owners(g, x) && OG.is_valid_owners(g, w)

    @test OG.remove_edge!(g, w, x; rule = :test)
    @test !OG.remove_edge!(g, x, w; rule = :test)   # ya no está
    @test g.removed_by[:test] == 1
    @test !OG.has_edge(g, x, w) && !OG.has_edge(g, w, x)
    @test isempty(g.edges)
    # la línea queda vacía y se ve
    @test haskey(g.inc[x], 1) && isempty(g.inc[x][1])
    @test !OG.is_valid_owners(g, x) && !OG.is_valid_owners(g, w)
    @test OG.check_invariants(g)
end

@testset "OwnersGraph: paso sin línea invalida" begin
    g = og_with_steps(3)
    x, w = og_id(0, 0), og_id(1, 0)
    OG.register!(g, x); OG.register!(g, w)
    OG.add_edge!(g, x, w)
    @test !OG.is_valid_owners(g, x)            # nada en el paso 2
    z = og_id(2, 0)
    OG.register!(g, z)
    OG.add_edge!(g, x, z); OG.add_edge!(g, w, z)
    @test OG.is_valid_owners(g, x) && OG.is_valid_owners(g, w) && OG.is_valid_owners(g, z)
end

@testset "OwnersGraph: remove_node!" begin
    g = og_with_steps(2)
    a, b, c = og_id(0, 0), og_id(1, 0), og_id(1, 1)
    for x in (a, b, c); OG.register!(g, x); end
    OG.add_edge!(g, a, b); OG.add_edge!(g, a, c)

    OG.remove_node!(g, b; rule = :clean)
    @test !OG.is_alive(g, b)
    @test !(b in g.alive[1])
    @test !OG.has_edge(g, a, b)
    @test OG.has_edge(g, a, c)
    @test g.removed_by[:clean] == 1
    @test g.valid                              # el paso 1 aún tiene a c
    @test OG.check_invariants(g)

    OG.remove_node!(g, c; rule = :clean)
    @test !g.valid                             # el paso 1 se queda sin vivos
    @test isempty(g.edges)
    @test !OG.is_valid_owners(g, a)
    @test OG.check_invariants(g)
    OG.remove_node!(g, c)                      # quitar un muerto es inocuo
    @test OG.check_invariants(g)
end

#=
    a      a'        paso 0
    |      |
    b      c         paso 1
     \    /
       d             paso 2
=#
function og_diamond()
    a, a2, b, c, d = og_id(0, 0), og_id(0, 1), og_id(1, 0), og_id(1, 1), og_id(2, 0)
    g = og_with_steps(1)
    OG.register!(g, a); OG.register!(g, a2)
    OG.add_step!(g)
    OG.create_from_parents!(g, b, [a])
    OG.create_from_parents!(g, c, [a2])
    OG.add_step!(g)
    OG.create_from_parents!(g, d, [b, c])
    return g, (a, a2, b, c, d)
end

@testset "OwnersGraph: create_from_parents!" begin
    g, (a, a2, b, c, d) = og_diamond()
    @test OG.check_invariants(g)
    @test Set(OG.neighbors_all(g, b)) == Set([a, b, d])       # d llega por simetría
    @test Set(OG.neighbors_all(g, c)) == Set([a2, c, d])
    @test Set(OG.neighbors_all(g, d)) == Set([a, a2, b, c, d])
    @test Set(OG.neighbors_all(g, a)) == Set([a, b, d])       # simétrica al construirla
    @test !OG.has_edge(g, b, c)                               # hermanos: sin arista
    @test length(g.edges) == 6
    @test all(x -> OG.is_valid_owners(g, x), (a, a2, b, c, d))
end

@testset "OwnersGraph: create_from_parents! solo toma vivos" begin
    a, a2, b = og_id(0, 0), og_id(0, 1), og_id(1, 0)
    g = og_with_steps(1)
    OG.register!(g, a); OG.register!(g, a2)
    OG.add_edge!(g, a, a2)                                    # arista artificial en el paso 0
    OG.add_step!(g)
    OG.remove_node!(g, a2)
    OG.create_from_parents!(g, b, [a])
    @test Set(OG.neighbors_all(g, b)) == Set([a, b])
    @test OG.check_invariants(g)
end

@testset "OwnersGraph: create_from_parents!, hermanos con padre común" begin
    a, b, c = og_id(0, 0), og_id(1, 0), og_id(1, 1)
    g = og_with_steps(1)
    OG.register!(g, a)
    OG.add_step!(g)
    OG.create_from_parents!(g, b, [a])
    OG.create_from_parents!(g, c, [a])       # a ya tiene a b como vecino
    @test !OG.has_edge(g, b, c)
    @test Set(OG.neighbors_all(g, c)) == Set([a, c])
    @test Set(OG.neighbors_all(g, a)) == Set([a, b, c])
    @test OG.check_invariants(g)
end

@testset "OwnersGraph: cut_by_support!" begin
    g, (a, a2, b, c, d) = og_diamond()
    @test OG.cut_by_support!(g, d, [b, c]; rule = :parents) == 0   # todo apoyado

    OG.remove_edge!(g, c, a2; rule = :test)
    # a' ya no lo apoya ningún padre de d (b no lo tiene, c lo acaba de perder)
    @test OG.cut_by_support!(g, d, [b, c]; rule = :parents) == 1
    @test g.removed_by[:parents] == 1
    @test !OG.has_edge(g, d, a2) && !OG.has_edge(g, a2, d)          # espejo incluido
    @test OG.has_edge(g, d, a)                                      # a sigue apoyado por b
    @test OG.check_invariants(g)
end

@testset "OwnersGraph: union!" begin
    x, y, z = og_id(0, 0), og_id(1, 0), og_id(2, 0)
    ga = og_with_steps(2)
    OG.register!(ga, x); OG.register!(ga, y)
    OG.add_edge!(ga, x, y)
    e_xy = OG.get_edge(ga, x, y)

    gb = og_with_steps(3)
    for n in (x, y, z); OG.register!(gb, n); end
    OG.add_edge!(gb, x, y); OG.add_edge!(gb, y, z)

    OG.union!(ga, gb)
    @test ga.nsteps == 3
    @test OG.is_alive(ga, z)
    @test OG.has_edge(ga, y, z) && OG.has_edge(ga, x, y)
    @test OG.get_edge(ga, x, y) === e_xy                           # la común es la de ga
    @test length(ga.edges) == 2
    @test OG.check_invariants(ga)
    @test OG.check_invariants(gb)                                  # gb no se toca
    @test length(gb.edges) == 2
end

@testset "OwnersGraph: secuencias al azar contra un modelo de pares" begin
    rng = Xoshiro(20260927)
    for round in 1:200
        nsteps = rand(rng, 2:4)
        g = og_with_steps(nsteps)
        ids = [og_id(s, i) for s in 0:nsteps-1 for i in 0:rand(rng, 1:3)]
        for x in ids; OG.register!(g, x); end
        alive = Set(ids)
        pairs = Set{Set{PId}}()
        ok = true
        for _ in 1:40
            op = rand(rng, 1:10)
            x, w = rand(rng, ids), rand(rng, ids)
            if op <= 6
                if x != w && x in alive && w in alive
                    OG.add_edge!(g, x, w); push!(pairs, Set([x, w]))
                end
            elseif op <= 9
                x in alive && w in alive && OG.remove_edge!(g, x, w; rule = :rnd)
                delete!(pairs, Set([x, w]))
            else
                OG.remove_node!(g, x; rule = :rnd)
                delete!(alive, x)
                filter!(p -> !(x in p), pairs)
            end
            ok &= OG.check_invariants(g)
            ok &= all(OG.is_alive(g, v) == (v in alive) for v in ids)
            ok &= all(OG.has_edge(g, u, v) == (u == v || Set([u, v]) in pairs)
                      for u in alive for v in alive)
            ok &= length(g.edges) == length(pairs)
        end
        @test ok
    end
end

@testset "OwnersGraph: deepcopy por estructura" begin
    g, (a, a2, b, c, d) = og_diamond()
    h = deepcopy(g)
    @test OG.check_invariants(h)
    @test h.edges == g.edges || Set(keys(h.edges)) == Set(keys(g.edges))
    @test h.inc == g.inc && h.alive == g.alive && h.nsteps == g.nsteps
    OG.remove_node!(h, d)                       # la copia es independiente
    @test OG.is_alive(g, d) && OG.has_edge(g, d, a)
    @test OG.check_invariants(g) && OG.check_invariants(h)
    @test OG.get_edge(h, a, b) !== OG.get_edge(g, a, b)
end
