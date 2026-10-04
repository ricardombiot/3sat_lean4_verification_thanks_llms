module GraphMapBin
    #=
    Mapa binario (`bin`) con ventana prohibida. Véase docs/plans/bin-map.md.

    Estructura simétrica (pasos 0-indexados, n variables, m cláusulas):

        paso 0            : Fusión raíz (1 nodo, sin requires)
        paso 2v-1 (v=1..n): positivos ⟨2v-1,0⟩ "v=0", ⟨2v-1,1⟩ "v=1" — sin requires
        paso 2v   (v=1..n): negados   ⟨2v,i⟩ "!v=i", requiere ⟨2v-1, 1-i⟩
        paso 2n+1         : Fusión media
        paso 2n+2+3j      : L1_j (2 nodos); L1_j=b requiere ⟨step(l1), b⟩
        paso 2n+3+3j      : L2_j (2 nodos); L2_j=b requiere ⟨step(l2), b⟩
        paso 2n+4+3j      : L3_j (2 nodos); L3_j=b requiere ⟨step(l3), b⟩; ventana prohibida (0,0,0)
        paso 2n+3m+2      : Fusión final

    stepCount = 2n + 3m + 3. Cada cláusula son 3 pasos de 2 nodos; la disyunción se expresa
    prohibiendo la ventana (L1=0, L2=0, L3=0). Sin los "requires negados" del mapa clásico.
    =#

    using Main.AbsSat.Alias: Step, NodeId, IndexNode, SetNodesId, PathNodeId
    using Main.AbsSat.Alias

    using Main.AbsSat.DBDocuments.MapDocumentNode: MapDocNode
    using Main.AbsSat.DBDocuments.MapDocumentNode

    using Main.AbsSat.DBCollections.MapCollectionNodes: MapColNodesLine
    using Main.AbsSat.DBCollections.MapCollectionNodes

    using Main.AbsSat.DBCollections.MapCollectionLines: MapColLines
    using Main.AbsSat.DBCollections.MapCollectionLines

    using Main.AbsSat.DBCollections.MapCollectionVars: MapColVars
    using Main.AbsSat.DBCollections.MapCollectionVars

    mutable struct GMapBin
        table_lines :: MapColLines
        table_vars :: MapColVars
        literals_counter :: Int64
        clausule_counter :: Int64
        stage :: String
        step :: Step
        prohibited_windows :: Set{PathNodeId}
    end

    function new()
        table_lines = MapCollectionLines.new()
        table_vars = MapCollectionVars.new()
        literals_counter = 0
        clausule_counter = 0
        stage = "vars"
        step = Step(0)
        prohibited_windows = Set{PathNodeId}()
        gmap = GMapBin(table_lines, table_vars, literals_counter, clausule_counter,
                       stage, step, prohibited_windows)
        # Fusión raíz en el paso 0 (el mapa bin empieza por un fusión, por simetría).
        make_fusion_node!(gmap)
        return gmap
    end

    function get_ids_step(gmap :: GMapBin, step :: Step) :: SetNodesId
        return MapCollectionLines.get_ids_step(gmap.table_lines, step)
    end

    function for_each_node_step(gmap :: GMapBin, step :: Step, fn_each)
        #! [for] $ O(7) $
        for node_id in get_ids_step(gmap, step)
            node = get_node(gmap, node_id)
            fn_each(node)
        end
    end

    function get_node(gmap :: GMapBin, node_id :: NodeId) :: Union{MapDocNode, Nothing}
        return MapCollectionLines.get_node(gmap.table_lines, node_id)
    end

    # Distinto del clásico: el mapa bin tiene un fusión raíz en el paso 0, así que el paso 0 sí debe
    # poder enlazarse con la variable 1. El clásico usa `step-1 > 0` porque su paso 0 es la primera
    # variable, que no tiene padres.
    function get_ids_last_step(gmap :: GMapBin) :: SetNodesId
        if gmap.step > 0
            return MapCollectionLines.get_ids_step(gmap.table_lines, gmap.step-1)
        else
            return SetNodesId()
        end
    end

    function add_var!(gmap :: GMapBin, title :: String)
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

    function close_vars!(gmap :: GMapBin)
        if gmap.stage == "vars"
            make_fusion_node!(gmap)
            gmap.stage = "gates"
        end
    end

    function close_gates!(gmap :: GMapBin)
        if gmap.stage == "gates"
            make_fusion_node!(gmap)
            gmap.stage = "end"
        end
    end

    function make_fusion_node!(gmap :: GMapBin)
        node_fusion = MapDocumentNode.new((step=gmap.step,index=0),"FusionNode")
        MapCollectionLines.push_node!(gmap.table_lines,node_fusion)

        #! [for] $ O(7) $
        for parent_id in get_ids_last_step(gmap)
            MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node_fusion.id)
        end

        gmap.step += 1
    end

    #=
    Cada cláusula ocupa tres pasos consecutivos (L1, L2, L3). Cada paso tiene dos nodos, uno por
    valor (0/1) del literal correspondiente; el nodo `Lp=b` requiere el literal `lp` con valor `b`.
    Al final de los tres se registra la ventana prohibida (L1=0, L2=0, L3=0), que el UP filtrará.
    =#
    function add_gate_bin!(gmap :: GMapBin, title_a :: String, title_b :: String, title_c :: String)
        if gmap.stage == "gates"
            step_a = MapCollectionVars.get_step_var(gmap.table_vars, title_a)
            step_b = MapCollectionVars.get_step_var(gmap.table_vars, title_b)
            step_c = MapCollectionVars.get_step_var(gmap.table_vars, title_c)

            # L1 (literal a)
            for b in 0:1
                node = MapDocumentNode.new((step=gmap.step,index=b),
                                           "or$(gmap.clausule_counter)_$(title_a)=$b")
                MapDocumentNode.add_require!(node, (step=step_a,index=b))
                MapCollectionLines.push_node!(gmap.table_lines, node)
                for parent_id in get_ids_last_step(gmap)
                    MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node.id)
                end
            end
            step_l1 = gmap.step
            gmap.step += 1

            # L2 (literal b)
            for b in 0:1
                node = MapDocumentNode.new((step=gmap.step,index=b),
                                           "or$(gmap.clausule_counter)_$(title_b)=$b")
                MapDocumentNode.add_require!(node, (step=step_b,index=b))
                MapCollectionLines.push_node!(gmap.table_lines, node)
                for parent_id in get_ids_last_step(gmap)
                    MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node.id)
                end
            end
            step_l2 = gmap.step
            gmap.step += 1

            # L3 (literal c), con ventana prohibida (0,0,0)
            for b in 0:1
                node = MapDocumentNode.new((step=gmap.step,index=b),
                                           "or$(gmap.clausule_counter)_$(title_c)=$b")
                MapDocumentNode.add_require!(node, (step=step_c,index=b))
                MapCollectionLines.push_node!(gmap.table_lines, node)
                for parent_id in get_ids_last_step(gmap)
                    MapCollectionLines.link_nodes!(gmap.table_lines, parent_id, node.id)
                end
            end
            step_l3 = gmap.step
            gmap.step += 1

            # Ventana prohibida: L1=0 ∧ L2=0 ∧ L3=0 no existe.
            push!(gmap.prohibited_windows,
                  PathNodeId((step=step_l1,index=0), (step=step_l2,index=0), (step=step_l3,index=0)))

            gmap.clausule_counter += 1
        else
            close_vars!(gmap)
            add_gate_bin!(gmap, title_a, title_b, title_c)
        end
    end

    include("./graph_map_bin_import_cnf.jl")

end
