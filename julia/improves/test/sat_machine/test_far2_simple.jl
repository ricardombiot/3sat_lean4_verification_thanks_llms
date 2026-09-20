using Test

# Test simple para far2.cnf
# Uso: julia --project=. -e 'include("src/main.jl"); include("test/sat_machine/test_far2_simple.jl")'

function test_far2_simple()
    println("\n" * "="^60)
    println("TEST: far2.cnf (incompatibilities)")
    println("="^60)

    cnf_path = "./example_cnf/far2.cnf"

    if !isfile(cnf_path)
        println("✗ Archivo $cnf_path no encontrado")
        return
    end

    println("✓ Cargando $cnf_path...")
    gmap = GraphMap.load_import!(cnf_path)

    println("✓ Ejecutando máquina...")
    machine = SatMachine.new(gmap)
    time_elapsed = @elapsed SatMachine.run!(machine)

    has_solution = SatMachine.have_solution(machine)

    println("\n[RESULTADOS]")
    println("   Tiempo: $(round(time_elapsed, digits=4)) s")
    println("   Solución: $has_solution")
    println("   Pasos: $(gmap.step)")

    @test has_solution == true
    println("\n✓ Test pasado")
end

test_far2_simple()
