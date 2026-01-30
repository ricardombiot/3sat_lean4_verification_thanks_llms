import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphMap.GraphMap
import AbsSat.Utils.ExhaustiveSolver
import AbsSat.SatMachine.Verification

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.Utils

def main : IO Unit := do
  IO.println "--- Starting Final Verification ---"

  -- 1. Theoretical/Runtime Invariants
  AbsSat.SatMachine.Verification.verification_tests

  -- 2. Integration Test
  IO.println "\n--- Starting SatMachine Integration Test ---"

  -- 1. Load CNF
  IO.println "Loading test.cnf..."
  let path := "test.cnf"
  if !(← System.FilePath.pathExists path) then
     IO.println "Error: test.cnf not found."
     return

  -- Use load_import!
  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! path

  IO.println s!"GMap Loaded. Step: {gmap.step}, Clauses: {gmap.clausule_counter}"

  -- 2. Create SatMachine
  let machine ← AbsSat.SatMachine.new gmap

  -- 3. Run
  IO.println "Running Machine..."
  AbsSat.SatMachine.run! machine

  -- 4. Check results
  let finished ← AbsSat.SatMachine.is_finished machine
  let found_solution ← AbsSat.SatMachine.have_solution machine

  IO.println s!"Finished: {finished}"
  IO.println s!"Have Solution: {found_solution}"

  if found_solution then
     IO.println "SatMachine successfully found a solution! ✅"
  else
     IO.println "SatMachine did NOT find a solution. ❌"
