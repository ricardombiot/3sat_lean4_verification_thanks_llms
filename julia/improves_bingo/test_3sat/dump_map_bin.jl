# Volcado canónico del mapa bin, para el diferencial con Lean (lean/improves_bin, `lake exe mapbin-dump`).
#
#   julia --project=.. dump_map_bin.jl OUTDIR f1.cnf f2.cnf ...
#
# Por cada fichero escribe OUTDIR/<nombre>.txt con una línea por hecho, sin orden (el script de
# comparación las ordena):
#   S <stepCount>
#   N <nodo> R <requires ordenados, separados por comas> O <sons ordenados>
#   W <ventana prohibida>
# Si el importador rechaza la fórmula, escribe una sola línea `SKIP <motivo>`.

include("./../src/main.jl")

keys_sorted(ids) = join(sort([Alias.as_key(id) for id in ids]), ",")

function dump_map(path :: String) :: Vector{String}
    gmap = try
        GraphMapBin.load_import_bin!(path)
    catch e
        return ["SKIP $(replace(sprint(showerror, e), '\n' => ' '))"]
    end
    lines = ["S $(gmap.step)"]
    for step in 0:gmap.step-1
        for id in GraphMapBin.get_ids_step(gmap, Step(step))
            node = GraphMapBin.get_node(gmap, id)
            push!(lines, "N $(Alias.as_key(id)) R $(keys_sorted(node.requires)) O $(keys_sorted(node.sons))")
        end
    end
    for w in gmap.prohibited_windows
        push!(lines, "W $(Alias.as_key(w))")
    end
    return lines
end

function main(args)
    outdir = args[1]
    mkpath(outdir)
    for path in args[2:end]
        name = replace(basename(path), ".cnf" => ".txt")
        write(joinpath(outdir, name), join(dump_map(path), "\n") * "\n")
    end
end

main(ARGS)
