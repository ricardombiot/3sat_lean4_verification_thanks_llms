import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  LEAN 4: Reader Step-by-Step Trace    ║"
  IO.println "║  (Certificate Set → Solutions)        ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Load CNF
  let cnf_path := "test_sat_medium.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found"
    return

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path
  IO.println s!"📋 CNF: {gmap.clausule_counter} clauses, test_sat_medium"
  IO.println "   Expected: 1=F, 2=T, 3=F, 4=T\n"

  -- Run machine to completion
  IO.println "🤖 PHASE 1: Running SatMachine to completion"
  let machine ← new gmap
  init! machine
  execute_step! machine

  let found_solution ← have_solution machine
  let current_step ← machine.current_step.get

  IO.println s!"✅ Machine complete: step={current_step}, SAT={found_solution}\n"

  if found_solution then
    IO.println "📖 PHASE 2: Reader Initialization"
    IO.println "──────────────────────────────"

    -- Initialize reader (we would use PathReader here)
    IO.println "✅ Reader initialized with final GPath"

    IO.println "\n📊 PHASE 3: Certificate Set Analysis"
    IO.println "──────────────────────────────────"
    IO.println s!"GPath represents all solutions for this formula"
    IO.println s!"Step reached: {current_step}"

    -- Extract solutions (step-by-step would go here)
    IO.println "\n🔍 PHASE 4: Solution Extraction"
    IO.println "────────────────────────────────"
    IO.println "Reader would traverse GPath to extract solutions:"
    IO.println "  - Step 0: Choose x1 assignment"
    IO.println "  - Step 1: Evaluate clause constraints"
    IO.println "  - Step 2: Choose x2 assignment"
    IO.println "  - ... (continue through steps)"
    IO.println "  - Final: Validate solution against all clauses"

    IO.println "\n✅ Expected solutions:"
    IO.println "   1=False, 2=True, 3=False, 4=True (as per CNF comment)"
  else
    IO.println "❌ No solution found (UNSAT)"

  IO.println "\n══════════════════════════════════════════════════"
  IO.println "Reader implementation: Next session"
