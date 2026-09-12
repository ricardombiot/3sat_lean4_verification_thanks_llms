import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader.PathReader
open AbsSat.Db.Machine.Cols.ColTimeline

def solution_to_binary (solution : Array Bool) : String :=
  String.intercalate "" (solution.toList.map (fun b => if b then "1" else "0"))

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Pigeonhole Reader Main (PHP 2,3)    ║"
  IO.println "║  Variable Names: x_ij (pigeon in hole)║"
  IO.println "╚════════════════════════════════════════╝\n"

  let cnf_path := "pigeonhole.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found"
    return

  IO.println "Loading formula..."
  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path

  IO.println "Initializing machine..."
  let machine ← new gmap
  init! machine

  IO.println "Executing SAT machine...\n"
  execute_step! machine

  let found_solution ← have_solution machine
  let current_step ← machine.current_step.get

  IO.println s!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"Machine Status: Step {current_step}"
  IO.println s!"Formula satisfiable: {found_solution}"
  IO.println s!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"

  if !found_solution then
    IO.println "✅ UNSATISFIABLE"
    IO.println "   PHP(2,3) correctly identified as unsatisfiable"
    IO.println "   (Cannot place 3 pigeons in 2 holes)\n"
  else
    IO.println "⚠️  SATISFIABLE (extracting solutions...)\n"

    let timeline ← machine.timeline.get

    let all_gpaths : IO (Array GPath) := do
      let gpaths_ref ← IO.mkRef (#[] : Array GPath)
      for_each_gpath timeline current_step (fun gpath => do
        let current ← gpaths_ref.get
        gpaths_ref.set (current.push gpath)
      )
      gpaths_ref.get

    let gpaths ← all_gpaths
    IO.println s!"Found {gpaths.size} GPath(s) at step {current_step}\n"

    for (gpath_idx, gpath) in gpaths.toList.mapIdx (fun i g => (i, g)) do
      IO.println s!"GPath {gpath_idx}:"
      let solutions ← read_all_solutions! gpath
      IO.println s!"  Solutions found: {solutions.size}"

      if !solutions.isEmpty then
        IO.println "  First 10 solutions:"
        for (idx, solution) in solutions.toList.take 10 |>.mapIdx (fun i s => (i + 1, s)) do
          let binary := solution_to_binary solution
          IO.println s!"    {idx}. {binary}"
        if solutions.size > 10 then
          IO.println s!"    ... ({solutions.size - 10} more)"
      IO.println ""

  IO.println "Execution complete"
