function test_add_gates()
    gmap = GraphMap.new()

    GraphMap.add_var!(gmap, "x")
    GraphMap.add_var!(gmap, "y")
    GraphMap.add_var!(gmap, "w")
    GraphMap.add_gate!(gmap, "x","y","w")
    GraphMap.add_gate!(gmap, "x","!y","w")
    GraphMap.add_gate!(gmap, "x","y","!w")

    col_lines = gmap.table_lines

    #@test gmap.step == Step(2+2+2+1+1)


    diagram = GraphMapVisual.build(gmap)

    GraphMapVisual.to_png(diagram, "xyw_or0")
end

test_add_gates()
