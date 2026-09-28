# SecPair (src/graph_path/graph_path_secpair.jl, espejo de lean/improves_bingo/AbsSatBingo/Model/SecPair.lean).
@testset "SecPair" begin
    for f in ["simple3sat_v3_c2.cnf", "basic_v3_c1.cnf", "v4_c12_i1.cnf"]
        path = isfile(joinpath(@__DIR__, "../example_cnf", f)) ? joinpath(@__DIR__, "../example_cnf", f) :
               joinpath(@__DIR__, "../../test_window/instances", f)
        m = SatMachine.new(GraphMap.load_import!(path))
        redirect_stdout(devnull) do; SatMachine.run!(m); end
        g = first(SatMachine.get_gpath_solutions(m))
        # el estado final la cumple (medido en todo el corpus: probe_tri_sec.jl)
        @test GraphPath.pair_closed(g)                 # Lean PairClosed
        @test GraphPath.sec_pair(g)
        @test GraphPath.sec_pair(g; by = :node)
        # una arista falsa entre dos vivos sin entrada común en algún paso queda fuera de toda sección
        og = g.og
        ids = collect(GraphPath.alive_ids(g))
        fake = nothing
        for y in ids, w in ids
            (y == w || PathOwnersGraph.step_of(y) == PathOwnersGraph.step_of(w) || PathOwnersGraph.has_edge(og, y, w)) && continue
            g2 = deepcopy(g); PathOwnersGraph.add_edge!(g2.og, y, w)
            GraphPath.shares_every_step(g2.og, y, w) && continue
            fake = (g2, y, w); break
        end
        if fake !== nothing
            g2, y, w = fake
            bad = GraphPath.sec_pair_bad(g2.og)
            @test any(e -> Set(e) == Set((y, w)), bad)
        end
    end
end
