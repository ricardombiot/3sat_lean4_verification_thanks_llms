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
        @test GraphPath.edge_clique(g)                 # Lean EdgeClique
        @test GraphPath.sec_pair(g)
        @test GraphPath.sec_pair(g; by = :node)
        # Lean SecStruct: cada sección de un paso con elección está cerrada por enlaces y apoyo
        for k in 0:g.og.nsteps-1
            GraphPath.choice_at(g.og, k) || continue
            for b in unique(x.id for x in g.og.alive[k])
                xs = [x for x in g.og.alive[k] if x.id == b]
                adj = GraphPath.sec_fix!(GraphPath.sec_section(g.og, xs), g.og.nsteps)
                @test GraphPath.sec_struct_fails(g, adj) == (0, 0, 0)
            end
        end
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
            @test GraphPath.edge_clique_miss(g2) == (1, 0)   # la arista falsa no está en ninguna camarilla
        end
    end
end
