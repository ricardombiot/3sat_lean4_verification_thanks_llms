# StarOneSide (29-sept-2026, rama reader-stuck; Lean `StarSplit.lean`, pieza B2 `StarPure`).
#
#   PROBE_MAP=bin PROBE_ONLY=… julia --project=. test_3sat/probe_star_oneside.jl <salida.tsv>
#
# En cada join u = e ∪ g, para cada cima t de u (vive en el lado L), S(t) = vivos de u que posee t (con t). Para cada
# pareja y–w de u con y, w ∈ S(t) que NO es arista de L: ¿hay un paso l en el que ningún r ∈ S(t) posee (en u) a y y
# a w? Si sí para toda pareja, ninguna estructura cerrada dentro de la estrella puede usarla (B2 sale en una vuelta).
#   stars / both (t en los dos lados) / np (parejas que no son de L) / nf (sin paso sin testigo: StarOneSide falla)
#   dónde está el paso sin testigo (una pareja puede contar en varios): at_k (el paso del remitente k = T-2), above (por
#   encima del extremo más alto), between (entre los dos extremos), below (por debajo del más bajo); hi_is_k: el extremo
#   más alto está en k; at_hm1 / at_hp1: libre en el paso de los padres del más alto (hi-1) / justo encima (hi+1);
#   same: los dos en el mismo paso. nfreeL / nfree: pasos libres con aristas de L / de la unión; all_help0: parejas en
#   las que las aristas de fuera de L no ayudan en ningún paso libre de L; helped: pasos libres de L que la unión llena;
#   todo sin contar los pasos de los extremos; noLfree: sin paso interior libre con aristas de L. Padres (en L) del más alto: nopar (ninguno vivo), par_L (alguno posee al otro en L),
#   par_u (alguno lo posee en la unión), par_in_S (alguno está en la estrella)

const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))

using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
using .AbsSat.Probes

const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
alive(h) = Set(x for (_, xs) in h.og.alive for x in xs)
const SIDES = Ref{Any}(nothing)

function on_join_post(u)
    e, g = SIDES[]; SIDES[] = nothing
    u.current_step >= 2 || return
    og = u.og; top = u.current_step - 1
    Ae = alive(e); Ag = alive(g)
    for t in get(og.alive, top, SetPathNodesId())
        ine = t in Ae; ing = t in Ag
        ine && ing && bump(:both)
        L = ine ? e : g
        S = Set(z for z in alive(u) if PG.has_edge(og, z, t)); push!(S, t)
        bump(:stars)
        byl = Dict{Int, Vector{PathNodeId}}()
        for r in S
            push!(get!(byl, Int(r.id.step), PathNodeId[]), r)
        end
        for (y, w) in keys(og.edges)
            (y == w || !(y in S) || !(w in S) || PG.has_edge(L.og, y, w)) && continue
            bump(:np)
            free = [l for l in 0:u.current_step-1 if
                    all(r -> !(PG.has_edge(og, y, r) && PG.has_edge(og, w, r)), get(byl, l, PathNodeId[]))]
            if isempty(free)
                bump(:nf)
            else
                k = u.current_step - 2
                lo = min(Int(y.id.step), Int(w.id.step)); hi = max(Int(y.id.step), Int(w.id.step))
                k in free && bump(:at_k)
                any(l -> l > hi, free) && bump(:above)
                any(l -> lo < l < hi, free) && bump(:between)
                any(l -> l < lo, free) && bump(:below)
                (hi == k) && bump(:hi_is_k)
                # pasos libres usando solo aristas de L (testigos en S), sin los pasos de los extremos (allí el testigo es el
                # propio extremo y la pareja se atestigua a sí misma)
                ends = (Int(y.id.step), Int(w.id.step))
                freeL = [l for l in 0:u.current_step-1 if !(l in ends) &&
                         all(r -> !(PG.has_edge(L.og, y, r) && PG.has_edge(L.og, w, r)), get(byl, l, PathNodeId[]))]
                freeI = [l for l in free if !(l in ends)]
                isempty(freeL) && bump(:noLfree)               # con aristas de L hay testigo en todo paso interior
                bump(:nfreeL, length(freeL)); bump(:nfree, length(freeI))
                all(l -> l in freeI, freeL) && bump(:all_help0)   # el otro lado no llena ningún paso libre interior de L
                for l in freeL
                    l in freeI || bump(:helped)
                end
                (hi - 1) in free && bump(:at_hm1)
                (hi + 1) in free && bump(:at_hp1)
                (lo == hi) && bump(:same)
                # el más alto de la pareja y sus padres en e (documentos de L): ¿poseen al otro?
                yh = y.id.step >= w.id.step ? y : w; wl = yh == y ? w : y
                n = PathCollectionLines.get_node(L.table_lines, yh)
                if n !== nothing
                    ps = [q for q in n.parents if PG.is_alive(L.og, q)]
                    isempty(ps) && bump(:nopar)
                    any(q -> PG.has_edge(L.og, q, wl), ps) && bump(:par_L)
                    any(q -> PG.has_edge(og, q, wl), ps) && bump(:par_u)
                    any(q -> q in S, ps) && bump(:par_in_S)
                end
            end
        end
    end
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = (:stars, :both, :np, :nf, :at_k, :above, :between, :below, :hi_is_k, :at_hm1, :at_hp1, :same, :nopar, :par_L, :par_u, :par_in_S, :noLfree, :nfreeL, :nfree, :all_help0, :helped)
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus(skip = ["tseitin_petersen_H.cnf", "simple_v3_c2.cnf"],
                                                   dirs = [ProbeLib.DIRS[end]; ProbeLib.DIRS[1:end-1]])) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        machine = SatMachine.new(loader(path))
        t = @elapsed Probes.with(:join_pre => (a, b) -> (SIDES[] = (deepcopy(a), deepcopy(b))),
                                 :join_post => on_join_post) do
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
        end
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
