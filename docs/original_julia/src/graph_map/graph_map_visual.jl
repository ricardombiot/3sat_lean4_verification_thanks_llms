module GraphMapVisual

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId
    using Main.AbsSat.Alias

    using Main.AbsSat.DBDocuments.MapDocumentNode: MapDocNode
    using Main.AbsSat.DBDocuments.MapDocumentNode

    using Main.AbsSat.DBCollections.MapCollectionNodes: MapColNodesLine
    using Main.AbsSat.DBCollections.MapCollectionNodes

    using Main.AbsSat.DBCollections.MapCollectionLines: MapColLines
    using Main.AbsSat.DBCollections.MapCollectionLines

    using Main.AbsSat.DBCollections.MapCollectionVars: MapColVars
    using Main.AbsSat.DBCollections.MapCollectionVars

    using Main.AbsSat.GraphMap: GMap
    using Main.AbsSat.GraphMap

    mutable struct MapDiagram
        graph :: GMap
        dot_txt :: String
    end

    function build(graph :: GMap)
        txt = ""
        diagram = MapDiagram(graph,txt)
        build_diagram!(diagram)

        return diagram
    end

    function to_png(diagram :: MapDiagram, name :: String, path :: String = "./test_visual")
        txt = diagram.dot_txt
        input_file = "$path/$name.dot"
        output_file = "$path/$name.png"
        open(input_file, "w") do io
            print(io, txt)
        end
        run(`dot -Tpng $input_file -o $output_file`)
    end


    function build_diagram!(diagram :: MapDiagram)
        diagram.dot_txt *= "digraph G {\n"
        diagram.dot_txt *= "     compound=true \n"
        draw!(diagram)
        draw_relations!(diagram)
        diagram.dot_txt *= "}"
    end

    function draw!(diagram :: MapDiagram)
        for step in 0:diagram.graph.step-1
            draw_line!(diagram, step)
        end
    end

    function draw_line!(diagram :: MapDiagram, step :: Step)
        id = step


        diagram.dot_txt *= "subgraph cluster_line_$id {\n"
        diagram.dot_txt *= " style=filled;\n"
        diagram.dot_txt *= " color=lightgrey; \n"
        diagram.dot_txt *= "     node [style=filled,color=white]; \n"
        for node_id in MapCollectionLines.get_ids_step(diagram.graph.table_lines, step)
            node = MapCollectionLines.get_node(diagram.graph.table_lines, node_id)
            draw_node!(diagram, node)
        end
        diagram.dot_txt *= "\n"
        diagram.dot_txt *= "     fontsize=\"12\" \n"
        diagram.dot_txt *= "     label = \"Line $id \" \n"
        diagram.dot_txt *= " }\n"
    end

    function draw_node!(diagram :: MapDiagram, node :: MapDocNode)
        key = Alias.as_key(node.id)
        key_node = get_key_node(node.id)
        list_requires = to_list(node.requires)
        #list_using_me = to_list(node.using_me)

        node_label_html = "<$(node.title)<BR /> ID: $key <BR />"
        #node_label_html *= "Using: [$list_using_me]<BR />"

        node_label_html *= "Requires: [$list_requires] <BR />"
        #node_label_html *= "<BR /><FONT POINT-SIZE=\"8\">Parents: $parents_nodes_txt</FONT>"
        #node_label_html *= "<BR /><FONT POINT-SIZE=\"8\">Sons: $sons_nodes_txt</FONT>"
        #node_label_html *= owners_html

        #node_label_html *= draw_owners(node)
        node_label_html *= ">"

        diagram.dot_txt *=  "$key_node [label=$node_label_html]"
    end

    #=
    function draw_owners(node :: Node) :: String
        owners_text = ""
        for step in 0:node.owners.max_step
            if haskey(node.owners.table, step)
                mask = node.owners.table[step]
                owners_text *= "<BR /><FONT POINT-SIZE=\"10\"> $step:"
                for index in GraphOwnersMask.get_accepted_nodes(mask)
                    node_id :: NodeId = (step=step, index=index)
                    key_node = get_key_node(node_id)
                    owners_text *= "$key_node,"
                end
                owners_text *= "</FONT>"
            end
        end

        return owners_text
    end
    =#

    function draw_relations!(diagram :: MapDiagram)
        for step in 0:diagram.graph.step-1
            for node_id in MapCollectionLines.get_ids_step(diagram.graph.table_lines, step)
                node = MapCollectionLines.get_node(diagram.graph.table_lines, node_id)
                key_origin = get_key_node(node_id)
                for node_id_son in node.sons
                    key_destine = get_key_node(node_id_son)

                    diagram.dot_txt *=  "$key_origin -> $key_destine \n"
                end
            end
        end

    end

    function get_key_node(node_id :: NodeId) :: String
        return replace(Alias.as_key(node_id), "." => "_")
    end

    function to_list(set_nodes_id :: SetNodesId) :: String
        result = ""
        for node_id in set_nodes_id
            result *= Alias.as_key(node_id)
            result *= ","
        end
        return result
    end



end  # module GraphVisual
