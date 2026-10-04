# Veredicto de la máquina frente a fuerza bruta (instancias con ≤ 20 variables).
#   julia --project=../.. verdict_brute_probe.jl f1.cnf ...
include("./../../src/main.jl")
function brute(path)
    cls = Vector{Vector{Int}}(); nv = 0
    for l in eachline(path)
        s = strip(l); (isempty(s) || s[1] in ('c', '%')) && continue
        if s[1] == 'p'; nv = parse(Int, split(s)[3]); continue; end
        lits = [parse(Int, x) for x in split(s) if x != "0"]
        isempty(lits) || push!(cls, lits)
    end
    nv > 20 && return nothing
    for a in 0:(1 << nv) - 1
        all(c -> any(x -> ((a >> (abs(x) - 1)) & 1 == 1) == (x > 0), c), cls) && return true
    end
    false
end
ok = 0; bad = 0; skip = 0
for f in ARGS
    b = try brute(f) catch; nothing end
    b === nothing && (global skip += 1; continue)
    gmap = try GraphMapBin.load_import_bin!(f) catch; global skip += 1; continue end
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
    v = SatMachine.have_solution(m)
    if v == b; global ok += 1 else global bad += 1; println("DISTINTO $(basename(f)): máquina=$v fuerza bruta=$b") end
end
println("veredictos correctos: $ok, distintos: $bad, saltadas: $skip")
