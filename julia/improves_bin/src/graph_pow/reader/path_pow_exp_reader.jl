module PathPowExpReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.Alias

    using Main.AbsSat.GraphPow: GPow
    using Main.AbsSat.GraphPow

    using Main.AbsSat.GraphPow.PathPowReader: GPowReader
    using Main.AbsSat.GraphPow.PathPowReader

    mutable struct GPowExpReader
        list_readers :: Array{GPowReader,1}
        list_solutions :: Array{BitArray{1},1}
        is_finished :: Bool
    end

    function new(gpath :: GPow) :: GPowExpReader
        reader_seed = PathPowReader.new(gpath)
        list_readers = Array{GPowReader,1}()
        push!(list_readers, reader_seed)
        list_solutions = Array{BitArray{1},1}()
        is_finished = false

        GPowExpReader(list_readers, list_solutions, is_finished)
    end

    function read!(exp_reader :: GPowExpReader)
        while !exp_reader.is_finished
            read_step!(exp_reader)
        end
    end

    function read_step!(exp_reader :: GPowExpReader)
        if !exp_reader.is_finished
            is_finished = false
            new_list_readers = Array{GPowReader,1}()

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


    function make_step_register_and_filter!(reader :: GPowReader)
        PathPowReader.register_selection!(reader)
        PathPowReader.filter_gpath!(reader)
        reader.step += 2
    end

    function select_and_derive!(reader :: GPowReader) :: Array{GPowReader,1}
        derive_readers = Array{GPowReader,1}()
        for last_selected in reader.gpath.lines_table[reader.step]
            reader_copy = deepcopy(reader)

            map_id_node = last_selected.id
            reader_copy.last_selected = last_selected
            reader_copy.last_requires = SetNodesId([map_id_node])

            push!(derive_readers, reader_copy)
        end

        return derive_readers
    end


end
