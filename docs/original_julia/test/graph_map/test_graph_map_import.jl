function test_import()
    println("path: " * pwd())
    path_file = "./test/example_cnf/complete_v3.cnf"

    gmap = GraphMap.load_import!(path_file)

    diagram = GraphMapVisual.build(gmap)
    GraphMapVisual.to_png(diagram, "map_complete_v3", "./test/test_visual")
end

test_import()
