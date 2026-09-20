using Test
using Main.AbsSat.Alias
using Main.AbsSat.GraphMap
using Main.AbsSat.SatMachine
using Main.AbsSat.DBDocuments.PathDocumentOwners
using Main.AbsSat.DBDocuments.PathDocumentNode
using Main.AbsSat.DBCollections.PathCollectionLines
using Main.AbsSat.DBCollections.PathCollectionNodes
# ============================================================================
# TEST: tseitin_petersen_H (fórmula con owners incompatibles)
# ============================================================================

function test_tseitin_petersen_H()
    println("\n" * "="^80)
    println("TEST: tseitin_petersen_H (fórmula con zombies)")
    println("="^80)

    # Cargar tseitin_petersen_H.cnf
    cnf_path = "./test/example_cnf/tseitin_petersen_H.cnf"

    if !isfile(cnf_path)
        println("✗ Archivo $cnf_path no encontrado")
        return
    end

    println("✓ Cargando $cnf_path...")

    # Leer CNF y crear GMap
    gmap = GraphMap.load_import!(cnf_path)

    println("✓ GMap creado: $(gmap.step) pasos")

    # ===== PRUEBA 1: Review ESTÁNDAR =====
    println("\n[1] Ejecutando review ESTÁNDAR...")
    machine = SatMachine.new(gmap)
    time_std = @elapsed SatMachine.run!(machine)

    @test SatMachine.have_solution(machine) == false
    SatMachine.plot_gpaths(machine, "gpath_test_tseitin_petersen_H", "./test/test_visual/")

end

@testset "TseitinPetersenH" begin
    test_tseitin_petersen_H()
end
