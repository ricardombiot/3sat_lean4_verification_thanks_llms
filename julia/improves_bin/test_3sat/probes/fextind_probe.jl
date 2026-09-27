# Puentes para FExt por inducción (docs/context/ambfar.md §4.2ξ). Pins de nodos de mapa, uno tras otro con su review.
#   M1 (join):  J|R válido ⇒ ∃ pieza P_i|R válida.
#   M2 (bajar): P|R válido (P = upF X d) ⇒ X|(req(d) ++ R⁻) válido, R⁻ = R sin la cima.
#   M3 (subir): X|(req(d) ++ R⁻) válido ⇒ P|R⁻ válido.
#   Con la ventana (a, b) de los pasos s-1, s, no prohibida con d:
#   M2w: P|R válido ⇒ ∃ (a, b) no prohibida con X|(req ++ R⁻ ++ [a, b]) válido.
#   M3w: (a, b) no prohibida y X|(req ++ R⁻ ++ [a, b]) válido ⇒ P|(R⁻ ++ [a, b]) válido.
# R: vacío, todos los de un nodo, NR al azar de 2 y 3 nodos (pasos distintos).
#   julia --project=../.. fextind_probe.jl f1.cnf ...
include("./../../src/main.jl")
using Random
Random.seed!(parse(Int, get(ENV, "SEED", "89")))
const NR = parse(Int, get(ENV, "NR", "10"))
mapids(g) = (S = Set{NodeId}(); for (_, line) in g.table_lines.table, (pid_, _) in line.table; push!(S, pid_.id); end; collect(S))
function pinned(g, R)
    f = deepcopy(g)
    redirect_stdout(devnull) do
        f.review_owners = true; GraphPath.make_review_owners!(f)
        for r in R; f.is_valid && GraphPath.filter!(f, SetNodesId([r])); end
    end
    f
end
function sampleR(g)
    ids = mapids(g); bystep = Dict{Int, Vector{NodeId}}()
    for i in ids; push!(get!(bystep, i.step, NodeId[]), i); end
    Rs = Vector{Vector{NodeId}}([NodeId[]]); append!(Rs, [[i] for i in ids])
    for size in 2:3, _ in 1:NR
        ks = shuffle(collect(keys(bystep)))[1:min(size, length(bystep))]
        push!(Rs, [rand(bystep[s]) for s in ks])
    end
    Rs
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    bump(k) = (st[k] = get(st, k, 0) + 1)
    ex(s) = get(st, "ej", 0) < 8 && (bump("ej"); println(s))
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        pieces = Dict{NodeId, Vector{Any}}()
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            g.is_valid || return
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                p.is_valid || continue
                push!(get!(pieces, d, Any[]), p)
                get(ENV, "ONLY_M1", "0") == "1" && continue
                # M2 y M3 en la pieza
                req = collect(dn.requires)
                forb = SatMachine.map_prohibited(gmap)
                xids = mapids(g)
                W = s >= 1 ? [(a, b) for a in xids for b in xids if a.step == s - 1 && b.step == s &&
                              !(PathNodeId(a, b, d) in forb)] : Tuple{NodeId, NodeId}[]
                for R in sampleR(p)
                    s >= 1 || break
                    Rm = [r for r in R if r.step < s - 1]
                    if pinned(p, R).is_valid
                        okw = any(((a, b),) -> pinned(g, vcat(req, Rm, [a, b])).is_valid, W)
                        bump("M2w $(okw ? "ok" : "FALLA")"); okw || ex("M2w FALLA $(basename(path)) paso $s d=$d R=$R")
                    end
                    for (a, b) in W
                        pinned(g, vcat(req, Rm, [a, b])).is_valid || continue
                        ok3 = pinned(p, vcat(Rm, [a, b])).is_valid
                        bump("M3w $(ok3 ? "ok" : "FALLA")"); ok3 || ex("M3w FALLA $(basename(path)) paso $s d=$d R=$Rm w=$((a, b))")
                    end
                end
                for R in sampleR(p)
                    Rm = [r for r in R if r.step < s + 1]
                    pv = pinned(p, R).is_valid
                    xv = pinned(g, vcat(req, Rm)).is_valid
                    if pv
                        bump("M2 $(xv ? "ok" : "FALLA")"); xv || ex("M2 FALLA $(basename(path)) paso $s d=$d R=$R")
                    end
                    if xv && length(Rm) == length(R)
                        pmv = pinned(p, Rm).is_valid
                        bump("M3 $(pmv ? "ok" : "FALLA")"); pmv || ex("M3 FALLA $(basename(path)) paso $s d=$d R=$Rm")
                    end
                end
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        top = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, top, function (g)
            g.is_valid || return
            Ps = get(pieces, g.map_parent_id, Any[])
            isempty(Ps) && return
            tag = length(Ps) >= 2 ? "M1 (≥2 piezas)" : "M1 (1 pieza)"
            for R in sampleR(g)
                pinned(g, R).is_valid || continue
                ok = any(p -> pinned(p, R).is_valid, Ps)
                bump("$tag $(ok ? "ok" : "FALLA")"); ok || ex("M1 FALLA $(basename(path)) paso $top R=$R")
            end
        end)
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end
