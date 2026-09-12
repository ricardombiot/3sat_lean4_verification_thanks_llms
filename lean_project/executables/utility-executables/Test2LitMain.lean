import AbsSat.GraphMap.ImportCnf
import AbsSat.SatMachine.SatMachine

open AbsSat.GraphMap
open AbsSat.SatMachine

def main : IO Unit := do
  IO.println "Testing 2-literal CNF parsing..."
  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! "test_2lit.cnf"
  IO.println "CNF loaded successfully"

  let machine ← new gmap
  init! machine
  execute_step! machine

  let found ← have_solution machine
  IO.println s!"SAT: {found}"
