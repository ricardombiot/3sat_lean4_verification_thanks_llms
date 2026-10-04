# BORRADOR (3-oct-2026, rama reader-stuck; informe v225): el lector por separadores.
#
# Derivado de `src/graph_path/reader/path_reader.jl`. Mismo lector de un camino (elige el primer nodo vivo del paso y
# filtra), con un solo cambio: el ORDEN de las variables. Primero los separadores (variables que están en dos o más
# cláusulas), en el orden de su primera cláusula; después el resto, en orden creciente. La solución se guarda por
# índice de variable, no por orden de lectura.
#
# No está incluido en `AbsSat`: se carga con `include` después de `src/main.jl` (véase test_3sat/probe_reader_sep.jl).
module PathSepReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBCollections.PathCollectionLines
    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    """Separadores: las variables que aparecen en dos o más cláusulas, en el orden de su primera cláusula."""
    function separators(n :: Int, clauses :: Vector{Vector{Int}}) :: Vector{Int}
        count = zeros(Int, n)
        first_clause = fill(typemax(Int), n)
        for (j, c) in enumerate(clauses), v in unique(abs.(c))
            count[v] += 1
            first_clause[v] = min(first_clause[v], j)
        end
        return sort([v for v in 1:n if count[v] >= 2], by = v -> (first_clause[v], v))
    end

    """El orden de lectura: los separadores primero, después el resto en orden creciente."""
    read_order(n :: Int, seps :: Vector{Int}) :: Vector{Int} = vcat(seps, [v for v in 1:n if !(v in seps)])

    mutable struct GPathSepReader
        gpath :: GPath
        order :: Vector{Int}
        pos :: Int
        solution :: BitArray{1}
        is_finished :: Bool
    end

    """`n` variables y las cláusulas (literales con signo, desde 1) de la fórmula que generó `gpath`."""
    function new(gpath :: GPath, n :: Int, clauses :: Vector{Vector{Int}}; order = read_order(n, separators(n, clauses)))
        return GPathSepReader(gpath, order, 1, falses(n), false)
    end

    # Mapa bin: la variable `v` (desde 1) está en el paso 2v - 1 y el índice del nodo es su valor.
    var_step(v :: Int) :: Step = Step(2v - 1)

    """Un paso: fijar el primer nodo vivo del paso de la siguiente variable del orden y filtrar."""
    function read_step!(reader :: GPathSepReader; choose = first)
        reader.is_finished && return
        if reader.pos > length(reader.order)
            reader.is_finished = true
            return
        end
        v = reader.order[reader.pos]
        ids = collect(PathCollectionLines.get_ids_step(reader.gpath.table_lines, var_step(v)))
        isempty(ids) && throw("ReaderSep: sin nodos vivos en el paso de x$v")
        selected = choose(ids)
        reader.solution[v] = selected.id.index == 1
        GraphPath.filter!(reader.gpath, SetNodesId([selected.id]))
        reader.gpath.is_valid || throw("ReaderSep: GPATH INVALID tras fijar x$v")
        reader.pos += 1
    end

    function read!(reader :: GPathSepReader; choose = first) :: BitArray{1}
        while !reader.is_finished
            read_step!(reader; choose = choose)
        end
        return reader.solution
    end

end
