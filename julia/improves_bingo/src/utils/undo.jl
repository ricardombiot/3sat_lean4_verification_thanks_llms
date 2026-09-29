# Registro de deshacer (rama optimizations-undo). Mientras ACTIVE, cada mutador de GPath (grafo de owners,
# documentos y líneas de nodos) apunta cómo revertirse; rollback! los ejecuta en orden inverso y deja el
# gpath como estaba. Permite aplicar el UP sobre el gpath del remitente sin copiarlo: si sale inválido se
# deshace; si es válido se une al destino y se deshace (send_to_destine!).
# Solo hay una transacción a la vez (la máquina es secuencial).
module Undo
    const LOG = Vector{Any}()
    const ACTIVE = Ref(false)

    @inline active() = ACTIVE[]
    @inline record!(undo) = push!(LOG, undo)

    function begin!()
        @assert !ACTIVE[] && isempty(LOG) "transacción abierta"
        ACTIVE[] = true
    end

    stop!() = (ACTIVE[] = false)

    function rollback!()
        ACTIVE[] = false
        while !isempty(LOG)
            pop!(LOG)()
        end
    end
end
