function test_import()
    path_file = "./example_cnf/simple3sat_v3_c2.cnf"

    gmap = GraphMap.load_import!(path_file)

    diagram = GraphMapVisual.build(gmap)
    GraphMapVisual.to_png(diagram, "map_simple3sat_v3_c2")
end

test_import()
