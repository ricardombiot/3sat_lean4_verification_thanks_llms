module GraphPowVisual

    using Main.AbsSat.Alias: Step, NodeId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias

    using Main.AbsSat.GraphPow: GPow
    using Main.AbsSat.GraphPow

    mutable struct PathDiagram
        graph :: GPow
        dot_txt :: String
    end

    function build(graph :: GPow)
        txt = ""
        diagram = PathDiagram(graph,txt)
        build_diagram!(diagram)

        return diagram
    end

    function to_png(diagram :: PathDiagram, name :: String, path :: String = "./test_visual")
        txt = diagram.dot_txt
        input_file = "$path/$name.dot"
        output_file = "$path/$name.png"
        open(input_file, "w") do io
            print(io, txt)
        end
        run(`dot -Tpng $input_file -o $output_file`)
    end


    function build_diagram!(diagram :: PathDiagram)
        diagram.dot_txt *= "digraph G {\n"
        diagram.dot_txt *= "     compound=true \n"
        draw!(diagram)
        draw_relations!(diagram)
        diagram.dot_txt *= "}"
    end

    function draw!(diagram :: PathDiagram)
        for step in 0:diagram.graph.current_step-1
            draw_line!(diagram, step)
        end
    end

    function draw_line!(diagram :: PathDiagram, step :: Step)
        id = step

        diagram.dot_txt *= "subgraph cluster_line_$id {\n"
        diagram.dot_txt *= " style=filled;\n"
        diagram.dot_txt *= " color=lightgrey; \n"
        diagram.dot_txt *= "     node [style=filled,color=white]; \n"
        for node_id in diagram.graph.lines_table[step]
            draw_node!(diagram, node_id)
        end
        diagram.dot_txt *= "\n"
        diagram.dot_txt *= "     fontsize=\"12\" \n"
        diagram.dot_txt *= "     label = \"Line $id \" \n"
        diagram.dot_txt *= " }\n"
    end

    function draw_node!(diagram :: PathDiagram, path_id_node :: PathNodeId)
        key = Alias.as_key(path_id_node)
        key_node = get_key_node(path_id_node)
        title = ""
        #list_requires = to_list(node.requires)
        #list_using_me = to_list(node.using_me)

        node_label_html = "<$title<BR /> ID: $key <BR />"
        #node_label_html *= "Using: [$list_using_me]<BR />"

        #node_label_html *= "Requires: [$list_requires] <BR />"
        #node_label_html *= "<BR /><FONT POINT-SIZE=\"8\">Parents: $parents_nodes_txt</FONT>"
        #node_label_html *= "<BR /><FONT POINT-SIZE=\"8\">Sons: $sons_nodes_txt</FONT>"
        #node_label_html *= owners_html

        #node_label_html *= draw_owners(node)
        node_label_html *= ">"

        diagram.dot_txt *=  "$key_node [label=$node_label_html]"
    end

    #=
    function draw_owners(node :: PathDocNode) :: String
        owners_text = ""
        for step in 0:node.owners.max_step
            owners_text *= "<BR /><FONT POINT-SIZE=\"10\">  $step :"
            if haskey(node.owners.table, step)
                set_owners_line_a = PathDocumentOwners.get(node.owners, step)
                for node_id in set_owners_line_a
                    key_node = Alias.as_key(node_id)
                    owners_text *= "$key_node,"
                end
            end
            owners_text *= "</FONT>"
        end

        empty_steps = node.owners.empty_steps
        if !isempty(empty_steps)
            owners_text *= "<BR /><FONT POINT-SIZE=\"10\">  INVALID STEPS:"
            for step in node.owners.empty_steps
                owners_text *= "$step,"
            end
            owners_text *= "</FONT>"
        end

        return owners_text
    end
    =#

    function draw_relations!(diagram :: PathDiagram)
        for step in 0:diagram.graph.current_step-1
            for node_id in diagram.graph.lines_table[step]
                key_origin = get_key_node(node_id)
                for node_id_son in GraphPow.get_node_sons_owners(diagram.graph, node_id)
                    key_destine = get_key_node(node_id_son)

                    diagram.dot_txt *=  "$key_origin -> $key_destine \n"
                end
            end
        end

    end

    function get_key_node(node_id :: PathNodeId) :: String
        return replace(Alias.as_key(node_id), "." => "_")
    end

    function to_list(set_nodes_id :: SetPathNodesId) :: String
        result = ""
        for node_id in set_nodes_id
            result *= Alias.as_key(node_id)
            result *= ","
        end
        return result
    end



end  # module GraphVisual
