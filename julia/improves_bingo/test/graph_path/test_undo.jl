# up_in_place! + undo_up! (rama optimizations-undo): deshacer deja el gpath exactamente como estaba, y el
# resultado del UP en sitio es el mismo que el del UP sobre una copia. Sobre los gpaths de la máquina, para
# cada envío (origen, hijo), con y sin etiquetas por fila.

function undo_fingerprint(g :: GPath)
    og = g.og
    edges = Dict(k => (e.a, e.b, e.born, copy(e.tags)) for (k, e) in og.edges)
    inc = Dict(x => Dict(s => copy(ws) for (s, ws) in r) for (x, r) in og.inc)
    lines = Dict(s => (l.step, l.count, l.is_valid, copy(l.node_ids),
                       Dict(id => (n.id, n.title, copy(n.parents), copy(n.sons)) for (id, n) in l.table))
                 for (s, l) in g.table_lines.table)
    return (Dict(s => copy(v) for (s, v) in og.alive), edges, inc, Dict(x => copy(t) for (x, t) in og.ntags),
            og.nsteps, og.valid, og.krows, lines, g.table_lines.is_valid,
            g.current_step, g.map_parent_id, g.review_owners, g.is_valid)
end

function undo_check_instance(path :: String)
    machine = SatMachine.new(GraphMap.load_import!(path))
    SatMachine.init!(machine)
    bad = 0; sends = 0; valid = 0
    while true
        SatMachine.have_gpaths_step(machine) || break
        gs = SatMachine.get_gpath_list(machine)
        for g in gs
            node = SatMachine.map_get_node(machine.gmap, g.map_parent_id)
            for id_destine in node.sons
                d = SatMachine.map_get_node(machine.gmap, id_destine)
                proh = SatMachine.map_prohibited(machine.gmap)
                ref = GraphPath.copy_gpath(g)
                GraphPath.do_up_filtering!(ref, d.requires, id_destine, d.title, proh)
                before = undo_fingerprint(g)
                snap = GraphPath.up_in_place!(g, d.requires, id_destine, d.title, proh)
                same_result = g.is_valid == ref.is_valid &&
                              (!ref.is_valid || undo_fingerprint(g) == undo_fingerprint(ref))
                inv = !g.is_valid || PathOwnersGraph.check_invariants(g.og)
                GraphPath.undo_up!(g, snap)
                sends += 1; valid += ref.is_valid
                (same_result && inv && undo_fingerprint(g) == before && PathOwnersGraph.check_invariants(g.og)) || (bad += 1)
            end
        end
        SatMachine.is_finished(machine) && break
        SatMachine.make_step!(machine)
    end
    return bad, sends, valid
end

@testset "UndoUP" begin
    files = String[]
    for d in ["../test_window/instances", "../test_3sat/output/instances", "./example_cnf"]
        isdir(joinpath(@__DIR__, "..", d)) || continue
        for f in sort(readdir(joinpath(@__DIR__, "..", d)))
            endswith(f, ".cnf") && push!(files, joinpath(@__DIR__, "..", d, f))
        end
    end
    for mode in (:off, :on)
        PathOwnersGraph.ROW_TAGS[] = mode
        tot = 0; val = 0
        for p in files[1:min(end, 12)]
            bad, sends, valid = undo_check_instance(p)
            @test bad == 0
            tot += sends; val += valid
        end
        println("undo ($mode): $tot envíos, $val válidos, deshacer exacto en todos")
    end
    PathOwnersGraph.ROW_TAGS[] = :off
end
