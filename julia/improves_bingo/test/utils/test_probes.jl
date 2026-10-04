# Puntos de sonda (src/utils/probes.jl): sin activar no hacen nada ni evalúan argumentos; con `with` llaman al
# hook, y al salir se retiran.
using Main.AbsSat.Probes

probe_fn(x, log) = (Probes.@probe :test_point (push!(log, :arg_evaluated); x); x * 2)

@testset "Probes" begin
    log = Symbol[]
    seen = Int[]
    @test probe_fn(1, log) == 2
    @test isempty(log)                       # sin activar, el argumento ni se evalúa

    r = Probes.with(:test_point => x -> push!(seen, x)) do
        probe_fn(5, log) + probe_fn(7, log)
    end
    @test r == 24 && seen == [5, 7] && log == [:arg_evaluated, :arg_evaluated]

    empty!(seen)
    @test probe_fn(9, log) == 18 && isempty(seen)      # retirado al salir

    Probes.reset!()
    Probes.with(:test_point => x -> (Probes.bump!(:n); Probes.sample!(:v, x))) do
        for i in 1:4; probe_fn(i, log); end
    end
    @test Probes.counted(:n) == 4
    s = Probes.sampled(:v)
    @test (s.n, s.min, s.max, Probes.avg(s)) == (4, 1.0, 4.0, 2.5)
    @test Probes.counted(:nunca) == 0
end
