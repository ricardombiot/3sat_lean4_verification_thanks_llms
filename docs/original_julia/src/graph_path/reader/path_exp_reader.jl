module PathExpReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBDocuments.PathDocumentNode: PathDocNode
    using Main.AbsSat.DBDocuments.PathDocumentOwners: PathDocOwners
    using Main.AbsSat.DBCollections.PathCollectionNodes: PathColNodesLine
    using Main.AbsSat.DBCollections.PathCollectionLines: PathColLines


    using Main.AbsSat.Alias
    using Main.AbsSat.DBDocuments.PathDocumentNode
    using Main.AbsSat.DBDocuments.PathDocumentOwners
    using Main.AbsSat.DBCollections.PathCollectionNodes
    using Main.AbsSat.DBCollections.PathCollectionLines

    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    using Main.AbsSat.GraphPath.PathReader: GPathReader
    using Main.AbsSat.GraphPath.PathReader

    mutable struct GPathExpReader
        list_readers :: Array{GPathReader,1}
        list_solutions :: Array{BitArray{1},1}
        is_finished :: Bool
    end

    function new(gpath :: GPath) :: GPathExpReader
        reader_seed = PathReader.new(gpath)
        list_readers = Array{GPathReader,1}()
        push!(list_readers, reader_seed)
        list_solutions = Array{BitArray{1},1}()
        is_finished = false

        GPathExpReader(list_readers, list_solutions, is_finished)
    end

    function read!(exp_reader :: GPathExpReader)
        while !exp_reader.is_finished
            read_step!(exp_reader)
        end
    end

    function read_step!(exp_reader :: GPathExpReader)
        if !exp_reader.is_finished
            is_finished = false
            new_list_readers = Array{GPathReader,1}()

            for reader in exp_reader.list_readers
                for derive_reader in select_and_derive!(reader)
                    make_step_register_and_filter!(derive_reader)
                    push!(new_list_readers, derive_reader)

                    if derive_reader.is_finished
                        push!(exp_reader.list_solutions, derive_reader.solution)
                        is_finished = true
                    end
                end
            end

            exp_reader.list_readers = new_list_readers
            exp_reader.is_finished = is_finished
        end
    end


    function make_step_register_and_filter!(reader :: GPathReader)
        PathReader.register_selection!(reader)
        PathReader.filter_gpath!(reader)
        reader.step += 2
    end

    function select_and_derive!(reader :: GPathReader) :: Array{GPathReader,1}
        derive_readers = Array{GPathReader,1}()
        ids = PathCollectionLines.get_ids_step(reader.gpath.table_lines, reader.step)
        for last_selected in ids
            reader_copy = deepcopy(reader)

            map_id_node = last_selected.id
            reader_copy.last_selected = last_selected
            reader_copy.last_requires = SetNodesId([map_id_node])

            push!(derive_readers, reader_copy)
        end

        return derive_readers
    end


end
