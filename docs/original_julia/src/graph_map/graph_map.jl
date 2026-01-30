module GraphMap

    using Main.AbsSat.Alias: Step, NodeId, IndexNode, SetNodesId
    using Main.AbsSat.DBDocuments.MapDocumentNode: MapDocNode
    using Main.AbsSat.DBDocuments.MapDocumentNode

    using Main.AbsSat.DBCollections.MapCollectionNodes: MapColNodesLine
    using Main.AbsSat.DBCollections.MapCollectionNodes

    using Main.AbsSat.DBCollections.MapCollectionLines: MapColLines
    using Main.AbsSat.DBCollections.MapCollectionLines

    using Main.AbsSat.DBCollections.MapCollectionVars: MapColVars
    using Main.AbsSat.DBCollections.MapCollectionVars

    mutable struct GMap
        table_lines :: MapColLines
        table_vars :: MapColVars
        literals_counter :: Int64
        clausule_counter :: Int64
        stage :: String
        step :: Step
    end

    function new()
        table_lines = MapCollectionLines.new()
        table_vars = MapCollectionVars.new()
        literals_counter = 0
        clausule_counter = 0
        stage = "vars"
        step = Step(0)
        GMap(table_lines, table_vars, literals_counter, clausule_counter, stage, step)
    end

    include("./graph_map_import_cnf.jl")

    function get_ids_step(gmap :: GMap, step :: Step) :: SetNodesId
        return MapCollectionLines.get_ids_step(gmap.table_lines, step)
    end

    function for_each_node_step(gmap :: GMap, step :: Step, fn_each)
        #! [for] $ O(7) $
        for node_id in get_ids_step(gmap, step)
            #node = MapCollectionLines.get_node(gmap.table_lines, node_id)
            node = get_node(gmap, node_id)
            fn_each(node)
        end
    end

    function get_node(gmap :: GMap, node_id :: NodeId) :: Union{MapDocNode, Nothing}
        return MapCollectionLines.get_node(gmap.table_lines, node_id)
    end

    function get_ids_last_step(gmap :: GMap) :: SetNodesId
        if gmap.step-1 > 0
            return MapCollectionLines.get_ids_step(gmap.table_lines, gmap.step-1)
        else
            return SetNodesId()
        end
    end

    function add_var!(gmap :: GMap , title :: String)
        if gmap.stage == "vars"
            var_step = gmap.step
            MapCollectionVars.register_var!(gmap.table_vars, title, var_step)
            var_neg_step = var_step+1
            var_parents = get_ids_last_step(gmap)
            # Positive Variable Nodes
            node0 = MapDocumentNode.new((step=var_step,index=0),"$title=0")
            MapDocumentNode.add_son!(node0, (step=var_neg_step,index=1))
            MapCollectionLines.push_node!(gmap.table_lines,node0)
            #
            node1 = MapDocumentNode.new((step=var_step,index=1),"$title=1")
            MapDocumentNode.add_son!(node1, (step=var_neg_step,index=0))
            MapCollectionLines.push_node!(gmap.table_lines,node1)

            #! [for] $ O(2) $
            for parent_id in var_parents
                MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node0.id)
                MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node1.id)
            end

            # Negative Variable Nodes
            node0_neg = MapDocumentNode.new((step=var_neg_step,index=0),"!$title=0")
            MapDocumentNode.add_parent!(node0_neg, (step=var_step,index=1))
            MapDocumentNode.add_require!(node0_neg, (step=var_step,index=1))
            MapCollectionLines.push_node!(gmap.table_lines,node0_neg)
            #
            node1_neg = MapDocumentNode.new((step=var_neg_step,index=1),"!$title=1")
            MapDocumentNode.add_parent!(node1_neg, (step=var_step,index=0))
            MapDocumentNode.add_require!(node1_neg, (step=var_step,index=0))
            MapCollectionLines.push_node!(gmap.table_lines,node1_neg)

            gmap.step += 2
            gmap.literals_counter += 2
        end
    end

    function close_vars!(gmap :: GMap)
        if gmap.stage == "vars"
            make_fusion_node!(gmap)

            gmap.stage = "gates"
        end
    end

    function close_gates!(gmap :: GMap)
        if gmap.stage == "gates"
            make_fusion_node!(gmap)

            gmap.stage = "end"
        end
    end

    function make_fusion_node!(gmap :: GMap)
        node_fusion = MapDocumentNode.new((step=gmap.step,index=0),"FusionNode")
        MapCollectionLines.push_node!(gmap.table_lines,node_fusion)

        #! [for] $ O(7) $
        for parent_id in get_ids_last_step(gmap)
            MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node_fusion.id)
        end

        gmap.step += 1
    end

    function add_gate!(gmap :: GMap, title_a :: String, title_b :: String, title_c :: String)
        if gmap.stage == "gates"
            step_a = MapCollectionVars.get_step_var(gmap.table_vars,title_a)
            step_b = MapCollectionVars.get_step_var(gmap.table_vars,title_b)
            step_c = MapCollectionVars.get_step_var(gmap.table_vars,title_c)

            valid_cases = ["001","010","011","100","101","110","111"]
            #! [for] $ O(7) $
            for case in valid_cases
                add_gate_case!(gmap, step_a, step_b, step_c, case)
            end

            gmap.clausule_counter += 1
            gmap.step += 1
        else
            close_vars!(gmap)
            add_gate!(gmap, title_a, title_b, title_c)
        end
    end

    function add_gate_case!(gmap :: GMap, step_a :: Step, step_b :: Step, step_c :: Step, case :: String)
        index = parse(Int64,case,base=2)
        title_or = "or$(gmap.clausule_counter)"
        node_gate = MapDocumentNode.new((step=gmap.step,index=index),"$title_or=$case")
        # target index value by case
        target_index_a = case[1] == '0' ? 0 : 1
        target_index_b = case[2] == '0' ? 0 : 1
        target_index_c = case[3] == '0' ? 0 : 1

        MapDocumentNode.add_require!(node_gate, (step=step_a,index=target_index_a))
        MapDocumentNode.add_require!(node_gate, (step=step_b,index=target_index_b))
        MapDocumentNode.add_require!(node_gate, (step=step_c,index=target_index_c))
        #
        MapCollectionLines.push_node!(gmap.table_lines, node_gate)

        #! [for] $ O(7) $
        for parent_id in get_ids_last_step(gmap)
            MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node_gate.id)
        end

    end

end
