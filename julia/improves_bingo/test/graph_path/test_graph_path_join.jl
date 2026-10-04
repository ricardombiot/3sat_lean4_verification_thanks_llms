function test_paths_join()
    gpath_x0 = GraphPath.new()
    GraphPath.do_up!(gpath_x0, (step=0,index=0),"x=0")
    GraphPath.do_up!(gpath_x0, (step=1,index=1),"!x=1")

    gpath_x0_y0 = deepcopy(gpath_x0)
    gpath_x0_y1 = deepcopy(gpath_x0)

    GraphPath.do_up!(gpath_x0_y0, (step=2,index=0),"y=0")
    GraphPath.do_up!(gpath_x0_y1, (step=2,index=1),"y=1")

    gpath_x1 = GraphPath.new()
    GraphPath.do_up!(gpath_x1, (step=0,index=1),"x=1")
    GraphPath.do_up!(gpath_x1, (step=1,index=0),"!x=0")

    gpath_x1_y0 = deepcopy(gpath_x1)
    gpath_x1_y1 = deepcopy(gpath_x1)

    GraphPath.do_up!(gpath_x1_y0, (step=2,index=0),"y=0")
    GraphPath.do_up!(gpath_x1_y1, (step=2,index=1),"y=1")

    gpath_y0 = deepcopy(gpath_x0_y0)
    GraphPath.do_join!(gpath_y0, gpath_x1_y0)
    GraphPath.do_up!(gpath_y0, (step=3,index=1),"!y=1")

    gpath_y1 = deepcopy(gpath_x0_y1)
    GraphPath.do_join!(gpath_y1, gpath_x1_y1)
    GraphPath.do_up!(gpath_y1, (step=3,index=0),"!y=0")

    diagram = GraphPathVisual.build(gpath_y0)
    GraphPathVisual.to_png(diagram, "gpath_y0")

    # Step 4

    gpath_y0_w0 = deepcopy(gpath_y0)
    gpath_y0_w1 = deepcopy(gpath_y0)

    GraphPath.do_up!(gpath_y0_w0, (step=4,index=0),"w=0")
    GraphPath.do_up!(gpath_y0_w1, (step=4,index=1),"w=1")

    gpath_y1_w0 = deepcopy(gpath_y1)
    gpath_y1_w1 = deepcopy(gpath_y1)

    GraphPath.do_up!(gpath_y1_w0, (step=4,index=0),"w=0")
    GraphPath.do_up!(gpath_y1_w1, (step=4,index=1),"w=1")

    gpath_w0 = deepcopy(gpath_y0_w0)
    GraphPath.do_join!(gpath_w0, gpath_y1_w0)
    GraphPath.do_up!(gpath_w0, (step=5,index=1),"!w=1")
    gpath_w1 = deepcopy(gpath_y0_w1)
    GraphPath.do_join!(gpath_w1, gpath_y1_w1)
    GraphPath.do_up!(gpath_w1, (step=5,index=0),"!w=0")

    diagram = GraphPathVisual.build(gpath_w0)
    GraphPathVisual.to_png(diagram, "gpath_w0")

    GraphPath.do_up!(gpath_w0, (step=6,index=0),"fusion")
    GraphPath.do_up!(gpath_w1, (step=6,index=0),"fusion")
    gpath_fusion =deepcopy(gpath_w0)
    GraphPath.do_join!(gpath_fusion, gpath_w1)

    diagram = GraphPathVisual.build(gpath_fusion)
    GraphPathVisual.to_png(diagram, "gpath_fusion")

    return gpath_fusion
end

function test_path_filter(gpath)
    requires = SetNodesId([(step=0,index=0)])
    GraphPath.filter!(gpath, requires)

    diagram = GraphPathVisual.build(gpath)
    GraphPathVisual.to_png(diagram, "gpath_select_x0")
end

gpath = test_paths_join()
test_path_filter(gpath)
