# BORRADOR (7-oct-2026, rama reader-window; informes v229-v230): el lector por nodos de ventana.
#
# Gemelo de `WinReading` (lean/improves_bingo/AbsSatBingo/Model/ForbidOnWinPin.lean): cada paso elige un nodo vivo `q`
# de un paso y fija su ventana entera `[abuelo, padre, q.id]` con UN solo filtro y UN review (`GraphPath.filter!` con
# los tres requisitos). Primero las ventanas de los terceros pasos de las cláusulas (que fijan los tres literales), en
# el orden pedido; después las de los pasos de las variables, que fijan lo que quede. La solución se lee del nodo que
# queda vivo en el paso de cada variable.
#
# Teorema que respalda (para la acolchada de un árbol de cláusulas, `padCnf`): `reader_winNode_tree` (ForbidOnPadLines,
# d7a4346): cualquier lectura de ventanas, en cualquier orden y con cualquier elección, no se atasca y queda dentro de
# una solución.
#
# No está incluido en `AbsSat`: se carga con `include` después de `src/main.jl` (véase test_3sat/probe_reader_win.jl).
module PathWinReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBCollections.PathCollectionLines
    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    # Mapa bin (como `varStep` y `clauseStep` en Lean, con variables y cláusulas desde 1).
    var_step(v :: Int) :: Step = Step(2v - 1)
    l3_step(n :: Int, j :: Int) :: Step = Step(2n + 3j + 1)

    """Los pasos de ventana a leer: los terceros pasos de las cláusulas en el orden `order` y después los pasos de las
    variables."""
    win_steps(n :: Int, order :: Vector{Int}) :: Vector{Step} = vcat([l3_step(n, j) for j in order], [var_step(v) for v in 1:n])

    mutable struct GPathWinReader
        gpath :: GPath
        n :: Int
        steps :: Vector{Step}
        pos :: Int
        is_finished :: Bool
    end

    new(gpath :: GPath, n :: Int, order :: Vector{Int}) = GPathWinReader(gpath, n, win_steps(n, order), 1, false)

    """La ventana entera de un nodo: abuelo, padre e id (los que existan)."""
    window(q :: PathNodeId) :: SetNodesId =
        SetNodesId([x for x in (q.gparent_id, q.parent_id, q.id) if x !== nothing])

    """Un paso: elegir un nodo vivo del paso de ventana siguiente y fijar su ventana con un filtro y un review."""
    function read_step!(reader :: GPathWinReader; choose = first)
        reader.is_finished && return
        if reader.pos > length(reader.steps)
            reader.is_finished = true
            return
        end
        s = reader.steps[reader.pos]
        ids = collect(PathCollectionLines.get_ids_step(reader.gpath.table_lines, s))
        isempty(ids) && throw("ReaderWin: sin nodos vivos en el paso $s")
        q = choose(sort(ids, by = string))
        GraphPath.filter!(reader.gpath, window(q))
        reader.gpath.is_valid || throw("ReaderWin: GPATH INVALID tras fijar la ventana del paso $s")
        reader.pos += 1
    end

    """La solución: el valor del nodo vivo en el paso de cada variable (tras leer todas las ventanas, uno solo)."""
    function solution(reader :: GPathWinReader) :: BitArray{1}
        sol = falses(reader.n)
        for v in 1:reader.n
            ids = collect(PathCollectionLines.get_ids_step(reader.gpath.table_lines, var_step(v)))
            length(unique(q -> q.id, ids)) == 1 || throw("ReaderWin: x$v sin fijar")
            sol[v] = first(ids).id.index == 1
        end
        return sol
    end

    function read!(reader :: GPathWinReader; choose = first) :: BitArray{1}
        while !reader.is_finished
            read_step!(reader; choose = choose)
        end
        return solution(reader)
    end

end
