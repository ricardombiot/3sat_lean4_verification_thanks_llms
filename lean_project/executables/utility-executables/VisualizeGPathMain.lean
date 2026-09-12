import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.GraphPathVisual
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.GraphPathVisual
open AbsSat.Db.Machine.Cols.ColTimeline

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Visualizing GPath: Certificate Set Φ  ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Load CNF
  let cnf_path := "simple_test.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found"
    return

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path
  IO.println s!"📋 CNF: {gmap.clausule_counter} clauses"

  -- Run machine
  IO.println "🤖 Running SatMachine to completion..."
  let machine ← new gmap
  init! machine
  execute_step! machine

  let _finished ← is_finished machine
  let found_solution ← have_solution machine
  let current_step ← machine.current_step.get

  IO.println s!"✅ Execution done: step={current_step}, SAT={found_solution}"

  -- Extract and visualize final GPath(s)
  IO.println "\n🎨 Certificate Set (Φ) Analysis:"
  if found_solution then
    let timeline ← machine.timeline.get
    for_each_gpath timeline (current_step - 1) (fun gpath => do
      let diagram := build gpath
      to_png! diagram "phi_final" "./output"
      stats! gpath
    )
    IO.println "\n✅ Diagram exported to ./output/phi_final.dot"
    IO.println "   (Render with: dot -Tpng phi_final.dot -o phi_final.png)"
  else
    IO.println "❌ Formula is UNSAT"
