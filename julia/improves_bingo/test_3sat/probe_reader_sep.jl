# El lector por separadores (3-oct-2026, rama reader-stuck; informe v225; borrador drafts/path_sep_reader.jl).
#
#   PROBE_MAP=bin PROBE_DIRS=../../lean/improves_bingo/scripts/cnf PROBE_ONLY=chain5_cross.cnf \
#     test_3sat/run_capped.sh 3500 7000 julia --heap-size-hint=3G --project=. test_3sat/probe_reader_sep.jl <salida.tsv>
#
# Con FORBID = :on, desde cada estado final de la máquina:
#   det_ok / det_stuck      el lector por separadores con la primera elección (como PathReader): solución / atasco
#   rnd_n / rnd_stuck / rnd_sat   SEP_RND lecturas con elección al azar en cada paso (semilla SEP_SEED)
#   ex_states / ex_t / ex_t_out / ex_e_out / ex_n_out   SEP_EXACT lecturas al azar juzgadas tras cada elección:
#                           triángulos sin prohibir, y triángulos / aristas / nodos fuera de toda camarilla
#   ex_t_out_sep / ex_t_out_int   triángulos fuera tras fijar un separador / una variable de dentro
using Random
const OUT = abspath(ARGS[1])
include(joinpath(@__DIR__, "..", "src/main.jl"))
include(joinpath(@__DIR__, "probes_lib.jl"))
include(joinpath(@__DIR__, "..", "drafts/path_sep_reader.jl"))
using .AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
const PG = PathOwnersGraph
const C = Dict{Symbol, Int}()
bump(k, n = 1) = (C[k] = get(C, k, 0) + n)
dump_partial() = open(OUT * ".partial", "w") do io
    for k in sort(collect(keys(C)), by = string)
        println(io, k, "\t", C[k])
    end
end
const SEP_RND = parse(Int, get(ENV, "SEP_RND", "40"))
const SEP_EXACT = parse(Int, get(ENV, "SEP_EXACT", "4"))
const SEP_SEED = parse(Int, get(ENV, "SEP_SEED", "1"))
const CAP = parse(Int, get(ENV, "EXACT_CAP", "50000"))

function load_cnf(path)
    n = 0; cls = Vector{Vector{Int}}()
    for line in eachline(path)
        s = strip(line); (isempty(s) || s[1] in ('c', '%')) && continue
        if s[1] == 'p'; n = parse(Int, split(s)[3]); continue; end
        l = [parse(Int, t) for t in split(s) if t != "0"]; isempty(l) || push!(cls, l)
    end
    return n, cls
end
sat(sol, cls) = all(c -> any(l -> (l > 0) == sol[abs(l)], c), cls)

# Juzgar un estado: nodos, aristas y triángulos fuera de toda camarilla.
function judge(g, tag)
    og = g.og
    top = Int(g.current_step) - 1
    alive = Dict(s => collect(get(og.alive, Step(s), SetPathNodesId())) for s in 0:top)
    N = Set{PathNodeId}(); E = Set{NTuple{2, PathNodeId}}(); T = Set{NTuple{3, PathNodeId}}()
    cliq = Ref(0); chain = PathNodeId[]
    ok(p) = all(w -> PG.has_edge(og, w, p), chain) &&
            !any(PG.dead_trio(og, chain[i], chain[j], p) for i in eachindex(chain) for j in (i + 1):length(chain))
    function dfs(x, s)
        cliq[] > CAP && return
        push!(chain, x)
        if s == 0
            cliq[] += 1
            L = length(chain)
            for i in 1:L
                push!(N, chain[i])
                for j in (i + 1):L
                    push!(E, (chain[j], chain[i]))
                    for k in (j + 1):L
                        push!(T, (chain[k], chain[j], chain[i]))
                    end
                end
            end
        else
            foreach(p -> dfs(p, s - 1), [p for p in alive[s - 1] if ok(p)])
        end
        pop!(chain)
    end
    foreach(t -> dfs(t, top), alive[top])
    if cliq[] > CAP
        bump(:ex_cap); return
    end
    bump(:ex_states)
    for sa in 0:top, a in alive[sa]
        a in N || bump(:ex_n_out)
        for sb in (sa + 1):top, b in PG.neighbors(og, a, Step(sb))
            PG.is_alive(og, b) || continue
            (a, b) in E || bump(:ex_e_out)
            for sr in (sb + 1):top, r in PG.neighbors(og, a, Step(sr))
                (PG.is_alive(og, r) && PG.has_edge(og, b, r)) || continue
                PG.dead_trio(og, a, b, r) && continue
                bump(:ex_t)
                if !((a, b, r) in T)
                    bump(:ex_t_out); bump(Symbol(:ex_t_out_, tag))
                end
            end
        end
    end
    dump_partial()
end

function main()
    _, loader, _ = ProbeLib.map_of_env()
    cols = [:n_seps, :det_ok, :det_stuck, :rnd_n, :rnd_stuck, :rnd_sat, :ex_states, :ex_cap, :ex_t, :ex_t_out,
            :ex_e_out, :ex_n_out, :ex_t_out_sep, :ex_t_out_int]
    header = "instance\ttruth\t" * join(string.(cols), "\t") * "\tsecs"
    ProbeLib.run_instances(OUT, header; files = ProbeLib.corpus()) do path, _
        ex = ProbeLib.exhaustive(path)
        truth = ex === nothing ? "?" : string(!isempty(ex))
        empty!(C)
        n, cls = load_cnf(path)
        seps = PathSepReader.separators(n, cls)
        C[:n_seps] = length(seps)
        PG.FORBID[] = :on
        machine = SatMachine.new(loader(path))
        t = @elapsed begin
            redirect_stdout(devnull) do
                SatMachine.run!(machine)
            end
            if SatMachine.have_solution(machine)
                rng = MersenneTwister(SEP_SEED)
                for g0 in SatMachine.get_gpath_solutions(machine)
                    # la primera elección, como PathReader
                    try
                        sol = PathSepReader.read!(PathSepReader.new(deepcopy(g0), n, cls))
                        sat(sol, cls) ? bump(:det_ok) : bump(:det_stuck)
                    catch
                        bump(:det_stuck)
                    end
                    # elecciones al azar
                    for _ in 1:SEP_RND
                        bump(:rnd_n)
                        try
                            sol = PathSepReader.read!(PathSepReader.new(deepcopy(g0), n, cls); choose = ids -> rand(rng, ids))
                            sat(sol, cls) && bump(:rnd_sat)
                        catch
                            bump(:rnd_stuck)
                        end
                        dump_partial()
                    end
                    # exactitud de los estados leídos
                    for _ in 1:SEP_EXACT
                        r = PathSepReader.new(deepcopy(g0), n, cls)
                        while !r.is_finished
                            v = r.pos <= length(r.order) ? r.order[r.pos] : 0
                            try
                                PathSepReader.read_step!(r; choose = ids -> rand(rng, ids))
                            catch
                                bump(:ex_stuck); break
                            end
                            r.is_finished || judge(r.gpath, v in seps ? :sep : :int)
                        end
                    end
                end
            end
        end
        PG.FORBID[] = :off
        return (truth, (get(C, c, 0) for c in cols)..., round(t, digits = 1))
    end
end

main()
