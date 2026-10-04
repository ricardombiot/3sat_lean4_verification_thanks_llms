# Puntos de sonda sin coste (rama probes-microframework). Un punto de sonda en src es
#
#     @probe :nombre arg1 arg2 …
#
# que expande a `enabled(Val(:nombre)) && hook(Val(:nombre), arg1, arg2, …)`. Por defecto `enabled` devuelve
# `false` para todo nombre: el compilador lo pliega y el punto desaparece (ni se evalúan los argumentos). Un
# probe lo activa con `Probes.with(:nombre => f, …) do … end`: la primera vez que se activa un nombre se
# definen sus métodos `enabled` (→ true) y `hook` (→ llama al `f` registrado), lo que recompila una vez los
# llamadores; al salir de `with` el `f` se retira y el punto vuelve a no hacer nada (aunque ya compilado con
# la guarda). El cuerpo corre con `invokelatest`, para ver los métodos recién definidos.
#
# Reglas: los hooks son de solo lectura sobre el estado de la máquina (con el UP en sitio, un gpath visto
# desde un hook puede estar a medias de un UP que se va a deshacer: quien necesite conservarlo, que lo copie).
# Los datos se acumulan con bump! / sample!, que solo se llaman desde hooks.
module Probes
    export @probe

    enabled(::Val) = false
    hook(::Val, args...) = nothing

    macro probe(name, args...)
        M = @__MODULE__
        :($M.enabled(Val($(esc(name)))) && $M.hook(Val($(esc(name))), $(map(esc, args)...)))
    end

    const SLOTS = Dict{Symbol, Base.RefValue{Any}}()

    function slot!(name :: Symbol) :: Base.RefValue{Any}
        get!(SLOTS, name) do
            ref = Ref{Any}(nothing)
            @eval begin
                enabled(::Val{$(QuoteNode(name))}) = true
                hook(::Val{$(QuoteNode(name))}, args...) = (f = $ref[]; f === nothing || f(args...); nothing)
            end
            ref
        end
    end

    """
        with(body, :nombre => f, …)

    Activa los hooks durante `body()` y los retira al salir.
    """
    function with(body, pairs :: Pair{Symbol, <:Any}...)
        refs = [(slot!(n), f) for (n, f) in pairs]
        for (ref, f) in refs; ref[] = f; end
        try
            return Base.invokelatest(body)
        finally
            for (ref, _) in refs; ref[] = nothing; end
        end
    end

    # ---------- acumuladores (solo desde hooks) ----------
    mutable struct Sample
        n :: Int
        sum :: Float64
        min :: Float64
        max :: Float64
    end
    Sample() = Sample(0, 0.0, Inf, -Inf)

    const COUNTS = Dict{Symbol, Int}()
    const SAMPLES = Dict{Symbol, Sample}()

    bump!(name :: Symbol, n :: Integer = 1) = (COUNTS[name] = get(COUNTS, name, 0) + n; nothing)

    function sample!(name :: Symbol, x :: Real)
        s = get!(SAMPLES, name) do; Sample(); end
        s.n += 1; s.sum += x; s.min = min(s.min, x); s.max = max(s.max, x)
        return nothing
    end

    counted(name :: Symbol) = get(COUNTS, name, 0)
    sampled(name :: Symbol) = get(SAMPLES, name, Sample())
    avg(s :: Sample) = s.n == 0 ? NaN : s.sum / s.n

    reset!() = (empty!(COUNTS); empty!(SAMPLES); nothing)
end
