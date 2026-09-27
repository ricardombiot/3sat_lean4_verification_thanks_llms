# F4 del plan docs/plans/graph_owners.md: compara dos volcados de dump_final.jl (improves_bin y
# improves_bingo). No carga ninguna máquina.
#
#   julia compare_bingo.jl <volcado de bin> <volcado de bingo>
#
# Por instancia: mismo veredicto, mismas soluciones y mismo estado final (nodos, global, y tabla,
# padres e hijos de cada nodo de cada gpath de la última línea). Si el estado difiere, cuenta las
# líneas distintas por tipo (owners, parents, sons, nodes, global) y enseña la primera.

function load_summary(dir)
    rows = Dict{String, Vector{String}}()
    for (i, l) in enumerate(eachline(joinpath(dir, "summary.tsv")))
        i == 1 && continue
        f = split(l, '\t')
        rows[f[1]] = f
    end
    return rows
end

# Las líneas del estado etiquetadas con su contexto (gpath y nodo), para contar diferencias por tipo.
function state_lines(path)
    out = Dict{String, String}()
    gp = ""; node = ""
    for l in eachline(path)
        s = strip(l)
        tag, rest = occursin(' ', s) ? split(s, ' '; limit = 2) : (s, "")
        if tag == "gpath"
            gp = rest; node = ""
            out["gpath|$gp"] = rest
        elseif tag == "node"
            node = rest
            out["node|$gp|$node"] = rest
        elseif tag in ("owners", "parents", "sons")
            out["$tag|$gp|$node"] = rest
        elseif tag in ("nodes", "global")
            out["$tag|$gp"] = rest
        else
            out["head|$s"] = s                     # veredicto, soluciones
        end
    end
    return out
end

function main(dir_a, dir_b)
    a, b = load_summary(dir_a), load_summary(dir_b)
    names = sort(collect(intersect(keys(a), keys(b))))
    n = 0; same_verdict = 0; same_sols = 0; same_state = 0; same_rounds = 0; errors = 0
    ta = 0.0; tb = 0.0
    kinds_total = Dict{String, Int}()
    for name in names
        ra, rb = a[name], b[name]
        if ra[3] == "ERROR" || rb[3] == "ERROR"
            errors += 1
            println("$name: ERROR bin=$(ra[3]) bingo=$(rb[3])")
            continue
        end
        n += 1
        same_verdict += ra[3] == rb[3]
        same_rounds += ra[6] == rb[6]
        ta += parse(Float64, ra[7]); tb += parse(Float64, rb[7])
        fa, fb = joinpath(dir_a, "$name.txt"), joinpath(dir_b, "$name.txt")
        la, lb = readlines(fa), readlines(fb)
        sa = la[1:findfirst(startswith("gpath"), vcat(la, ["gpath"]))-1]
        sb = lb[1:findfirst(startswith("gpath"), vcat(lb, ["gpath"]))-1]
        same_sols += sa == sb
        if la == lb
            same_state += 1
        else
            ma, mb = state_lines(fa), state_lines(fb)
            kinds = Dict{String, Int}()
            first_diff = ""
            for k in sort(collect(union(keys(ma), keys(mb))))
                get(ma, k, nothing) == get(mb, k, nothing) && continue
                kind = split(k, '|')[1]
                kinds[kind] = get(kinds, kind, 0) + 1
                kinds_total[kind] = get(kinds_total, kind, 0) + 1
                first_diff == "" && (first_diff = "$k\n      bin:   $(get(ma, k, "—"))\n      bingo: $(get(mb, k, "—"))")
            end
            println("$name: ESTADO DISTINTO $(kinds)\n    $first_diff")
        end
    end
    println("── $n instancias comparadas ($errors con error en alguna máquina)")
    println("   mismo veredicto $same_verdict, mismas soluciones $same_sols, mismo estado final $same_state, " *
            "mismas vueltas $same_rounds")
    isempty(kinds_total) || println("   líneas distintas por tipo: $kinds_total")
    println("   tiempo bin/bingo: $(round(ta, digits = 1)) / $(round(tb, digits = 1)) s")
end

main(ARGS[1], ARGS[2])
