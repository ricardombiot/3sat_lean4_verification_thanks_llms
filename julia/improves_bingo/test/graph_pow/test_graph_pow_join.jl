function test_paths_pow_join()
    gpath_x0 = GraphPow.new()
    GraphPow.do_up!(gpath_x0, (step=0,index=0))
    GraphPow.do_up!(gpath_x0, (step=1,index=1))

    gpath_x0_y0 = deepcopy(gpath_x0)
    gpath_x0_y1 = deepcopy(gpath_x0)

    GraphPow.do_up!(gpath_x0_y0, (step=2,index=0))
    GraphPow.do_up!(gpath_x0_y1, (step=2,index=1))

    gpath_x1 = GraphPow.new()
    GraphPow.do_up!(gpath_x1, (step=0,index=1))
    GraphPow.do_up!(gpath_x1, (step=1,index=0))

    gpath_x1_y0 = deepcopy(gpath_x1)
    gpath_x1_y1 = deepcopy(gpath_x1)

    GraphPow.do_up!(gpath_x1_y0, (step=2,index=0))
    GraphPow.do_up!(gpath_x1_y1, (step=2,index=1))

    gpath_y0 = deepcopy(gpath_x0_y0)
    GraphPow.do_join!(gpath_y0, gpath_x1_y0)
    GraphPow.do_up!(gpath_y0, (step=3,index=1))

    gpath_y1 = deepcopy(gpath_x0_y1)
    GraphPow.do_join!(gpath_y1, gpath_x1_y1)
    GraphPow.do_up!(gpath_y1, (step=3,index=0))

    diagram = GraphPowVisual.build(gpath_y0)
    GraphPowVisual.to_png(diagram, "gpath_pow_y0")

    # Step 4

    gpath_y0_w0 = deepcopy(gpath_y0)
    gpath_y0_w1 = deepcopy(gpath_y0)

    GraphPow.do_up!(gpath_y0_w0, (step=4,index=0))
    GraphPow.do_up!(gpath_y0_w1, (step=4,index=1))

    gpath_y1_w0 = deepcopy(gpath_y1)
    gpath_y1_w1 = deepcopy(gpath_y1)

    GraphPow.do_up!(gpath_y1_w0, (step=4,index=0))
    GraphPow.do_up!(gpath_y1_w1, (step=4,index=1))

    gpath_w0 = deepcopy(gpath_y0_w0)
    GraphPow.do_join!(gpath_w0, gpath_y1_w0)
    GraphPow.do_up!(gpath_w0, (step=5,index=1))
    gpath_w1 = deepcopy(gpath_y0_w1)
    GraphPow.do_join!(gpath_w1, gpath_y1_w1)
    GraphPow.do_up!(gpath_w1, (step=5,index=0))

    diagram = GraphPowVisual.build(gpath_w0)
    GraphPowVisual.to_png(diagram, "gpath_pow_w0")

    GraphPow.do_up!(gpath_w0, (step=6,index=0))
    GraphPow.do_up!(gpath_w1, (step=6,index=0))
    gpath_fusion =deepcopy(gpath_w0)
    GraphPow.do_join!(gpath_fusion, gpath_w1)

    diagram = GraphPowVisual.build(gpath_fusion)
    GraphPowVisual.to_png(diagram, "gpath_pow_fusion")

    return gpath_fusion
end

function test_path_pow_filter(gpath)
    requires = SetNodesId([(step=0,index=0)])
    GraphPow.filter!(gpath, requires)

    diagram = GraphPowVisual.build(gpath)
    GraphPowVisual.to_png(diagram, "gpath_pow_select_x0")
end

gpath = test_paths_pow_join()
test_path_pow_filter(gpath)
