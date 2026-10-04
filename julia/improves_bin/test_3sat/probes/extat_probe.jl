# Sonda de `ExtAt` / `ClauseChoice` (lean/improves_bin, ClauseWitness.lean) en la máquina Julia.
#
#   julia --project=../.. extat_probe.jl [--k3] f1.cnf f2.cnf ...
#
# En cada línea del L3 de una cláusula j (paso 2n+4+3j), con la relación `Owns` por entradas de la línea
# (unión de las tablas de todos los estados), recorre cliques Q con testigos en todos los pasos:
#   * todas las de tamaño 1 y 2 (nodos en pasos ≤ n), y con --k3 las de tamaño 3 de nodos de variable;
# y para cada una:
#   * semántica: ¿hay una asignación que cumple las cláusulas 0..j y pasa por Q (ventanas incluidas)?
#   * ExtAt: en cada paso de variable l, ¿hay x en l con x::Q clique y con testigos? Si no, para cada
#     candidato clique, el primer paso sin testigo y su tipo (var/mid/L1/L2/L3).
# Un Q con testigos y sin solución semántica es un fallo de `ClauseChoice`/`SemCert`.

include("./../../src/main.jl")

key(p) = Alias.as_key(p)

function read_cnf(path)
    nv = 0; cls = Vector{Vector{Int}}()
    for line in eachline(path)
        isempty(line) && continue
        c = line[1]
        (c == 'c' || c == '%') && continue
        if c == 'p'
            nv = parse(Int, split(line)[3])
        else
            lits = [parse(Int, t) for t in split(line) if t != "0"]
            length(lits) == 3 && push!(cls, lits)
        end
    end
    nv, cls
end

# selección de una asignación en cada paso (mapa bin, pasos 0-indexados)
function sel(a, s, nv, cls)
    if s == 0 || s == 2nv + 1 || s >= 2nv + 2 + 3length(cls)
        return (step = s, index = 0)
    elseif s <= 2nv
        v = (s + 1) ÷ 2
        return isodd(s) ? (step = s, index = Int(a[v])) : (step = s, index = 1 - Int(a[v]))
    else
        o = s - (2nv + 2); j = o ÷ 3 + 1; p = o % 3 + 1
        l = cls[j][p]
        val = l > 0 ? a[abs(l)] : !a[abs(l)]
        return (step = s, index = Int(val))
    end
end

function pid(a, s, nv, cls)
    p = s >= 1 ? sel(a, s - 1, nv, cls) : nothing
    g = s >= 2 ? sel(a, s - 2, nv, cls) : nothing
    PathNodeId(g, p, sel(a, s, nv, cls))
end

kind(s, nv, ncl) = s == 0 ? "root" : s <= 2nv ? "var" : s == 2nv + 1 ? "mid" :
    s < 2nv + 2 + 3ncl ? "L$((s - (2nv + 2)) % 3 + 1)" : "fin"

function union_owners(states)
    U = Dict{PathNodeId, Set{PathNodeId}}()
    for g in states, (_, line) in g.table_lines.table, (pid_, node) in line.table
        S = get!(U, pid_, Set{PathNodeId}())
        for (_, set) in node.owners.table
            union!(S, set)
        end
    end
    U
end

owns(U, r, q) = haskey(U, r) && (q in U[r])
isclique(U, Q) = all(q -> all(t -> owns(U, q, t), Q), Q)
function first_missing(U, bystep, Q, top)
    for l in 0:top
        any(r -> all(q -> owns(U, r, q), Q), get(bystep, l, PathNodeId[])) || return l
    end
    nothing
end

function probe_file(path; k3 = false, perstate = false)
    nv, cls = read_cnf(path)
    ncl = length(cls)
    gmap = GraphMapBin.load_import_bin!(path)
    machine = SatMachine.new(gmap)
    SatMachine.init!(machine)
    assigns = [BitVector(digits(m, base = 2, pad = nv)) for m in 0:(2^nv - 1)]
    sat(a, j) = all(c -> any(l -> (l > 0 ? a[abs(l)] : !a[abs(l)]), c), cls[1:j])
    stats = Dict{String, Int}()
    bump(k) = (stats[k] = get(stats, k, 0) + 1)
    examples = String[]
    while true
        s = machine.current_step
        o = s - (2nv + 2)
        isL3 = o >= 0 && s < 2nv + 2 + 3ncl && o % 3 == 2
        isLast = SatMachine.is_finished(machine)
        if isL3 || (perstate && isLast)
            j = isL3 ? o ÷ 3 + 1 : ncl   # cláusulas ya procesadas
            allstates = []
            CollectionTimeline.for_each_gpath(machine.timeline, s, g -> push!(allstates, g))
            groups = perstate ? [[g] for g in allstates] : [allstates]
            for states in groups
            U = union_owners(states)
            bystep = Dict{Int, Vector{PathNodeId}}()
            for r in keys(U); push!(get!(bystep, r.id.step, PathNodeId[]), r); end
            n = s - 1
            low = [r for r in keys(U) if r.id.step <= n]
            varn = [r for r in low if 1 <= r.id.step <= 2nv]
            Qs = Vector{Vector{PathNodeId}}()
            for x in low; push!(Qs, [x]); end
            for i in eachindex(low), k in i+1:length(low)
                low[i].id.step == low[k].id.step && continue
                push!(Qs, [low[i], low[k]])
            end
            if k3
                for i in eachindex(varn), k in i+1:length(varn), m in k+1:length(varn)
                    length(Set([varn[i].id.step, varn[k].id.step, varn[m].id.step])) == 3 || continue
                    push!(Qs, [varn[i], varn[k], varn[m]])
                end
            end
            good = [a for a in assigns if sat(a, j)]
            for Q in Qs
                isclique(U, Q) || continue
                first_missing(U, bystep, Q, s) === nothing || continue
                bump("Q con testigos (tamaño $(length(Q)))")
                semok = any(a -> all(q -> pid(a, q.id.step, nv, cls) == q, Q), good)
                if !semok
                    bump("FALLO semántico: Q con testigos sin solución (tamaño $(length(Q)))")
                    length(examples) < 5 && push!(examples, "$(basename(path)) L3=$s Q=$(map(key, Q))")
                end
                for l in (isLast ? (0:s) : (1:2nv))
                    any(q -> q.id.step == l, Q) && continue
                    cands = [x for x in get(bystep, l, PathNodeId[]) if isclique(U, vcat([x], Q))]
                    if isempty(cands)
                        bump("ExtAt: sin candidato clique")
                        continue
                    end
                    miss = [first_missing(U, bystep, vcat([x], Q), s) for x in cands]
                    if any(m -> m === nothing, miss)
                        bump("ExtAt ok")
                        # aprender: candidatos clique que NO extienden, ¿dónde les falta el testigo?
                        for (x, m) in zip(cands, miss)
                            m === nothing && continue
                            bump("  candidato descartado por testigo en paso $(kind(m, nv, ncl))")
                            # ¿bastarían las parejas? testigos de {x, q} para cada q
                            pairs = all(q -> first_missing(U, bystep, [x, q], s) === nothing, Q)
                            bump(pairs ? "    ...con testigos por parejas {x,q}" : "    ...sin testigos por parejas")
                            sem = any(a -> all(q -> pid(a, q.id.step, nv, cls) == q, vcat([x], Q)), good)
                            sem && bump("    !!! descartado pero con solución semántica")
                        end
                    else
                        bump("ExtAt FALLA")
                        length(examples) < 10 && push!(examples,
                            "$(basename(path)) L3=$s Q=$(map(key, Q)) l=$l faltas=$(miss)")
                    end
                end
            end
            end
        end
        (SatMachine.is_finished(machine) || !SatMachine.have_gpaths_step(machine)) && break
        redirect_stdout(devnull) do
            SatMachine.make_step!(machine)
        end
    end
    stats, examples
end

function main(args)
    k3 = "--k3" in args
    perstate = "--state" in args
    files = filter(a -> !startswith(a, "--"), args)
    println(perstate ? "modo: por estado (L3 y línea final)" : "modo: por entradas de la línea (L3)")
    total = Dict{String, Int}()
    exs = String[]
    for f in files
        st, ex = try
            probe_file(f; k3 = k3, perstate = perstate)
        catch e
            println("$(basename(f)): SALTADA ($(typeof(e)))"); continue
        end
        for (k, v) in st; total[k] = get(total, k, 0) + v; end
        append!(exs, ex)
        println("$(basename(f)): ", join(["$k=$v" for (k, v) in sort(collect(st))], "  "))
    end
    println("── total")
    for (k, v) in sort(collect(total)); println("  $k: $v"); end
    println("── ejemplos")
    foreach(println, exs[1:min(end, 15)])
end

main(ARGS)
