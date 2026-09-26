# LINK_MODE :off vs :on (enlaces caducados): mismo veredicto, estados y tiempo por instancia.
#   julia --project=../.. link_verdict_probe.jl f1.cnf ...
include("./../../src/main.jl")
function run(path, mode)
    GraphPath.LINK_MODE[] = mode
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    nst = 0; nn = 0
    t = @elapsed while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
        CollectionTimeline.for_each_gpath(m.timeline, m.current_step, g -> begin
            nst += 1
            for (_, line) in g.table_lines.table; nn += length(line.table); end
        end)
    end
    SatMachine.have_solution(m), nst, nn, t
end
dif = 0; same = 0; T = [0.0, 0.0]; N = [0, 0]
for f in ARGS
    try GraphMapBin.load_import_bin!(f) catch; println("  saltada $(basename(f))"); continue end
    a = run(f, :off); GraphPath.LINK_PRUNED[] = 0; b = run(f, :on)
    T[1] += a[4]; T[2] += b[4]; N[1] += a[3]; N[2] += b[3]
    if a[1] != b[1]; global dif += 1; println("VEREDICTO DISTINTO $(basename(f)): off=$(a[1]) on=$(b[1])")
    else global same += 1 end
    a[3] != b[3] && println("  $(basename(f)): nodos off=$(a[3]) on=$(b[3]), enlaces podados=$(GraphPath.LINK_PRUNED[])")
end
println("veredictos iguales: $same, distintos: $dif; nodos off=$(N[1]) on=$(N[2]); tiempo off=$(round(T[1],digits=1))s on=$(round(T[2],digits=1))s")
