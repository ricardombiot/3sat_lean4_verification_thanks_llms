import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader.PathReader
open AbsSat.Db.Machine.Cols.ColTimeline

def solution_to_coloring (solution : Array Bool) : String :=
  let v1 := if solution[0]! then "1" else if solution[1]! then "2" else "3"
  let v2 := if solution[3]! then "1" else if solution[4]! then "2" else "3"
  let v3 := if solution[6]! then "1" else if solution[7]! then "2" else "3"
  let v4 := if solution[9]! then "1" else if solution[10]! then "2" else "3"
  let v5 := if solution[12]! then "1" else if solution[13]! then "2" else "3"
  s!"v1={v1}, v2={v2}, v3={v3}, v4={v4}, v5={v5}"

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Graph Coloring Reader Main          ║"
  IO.println "║  5 vertices, 3 colors (5-3-COL)     ║"
  IO.println "╚════════════════════════════════════════╝\n"

  let cnf_path := "graph_coloring_3col.cnf"
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
    IO.println "No valid 3-coloring found"
  else
    IO.println "✅ Valid 3-colorings exist\n"

    let timeline ← machine.timeline.get

    let gpaths_ref ← IO.mkRef (#[] : Array GPath)
    for_each_gpath timeline current_step (fun gpath => do
      let current ← gpaths_ref.get
      gpaths_ref.set (current.push gpath)
    )
    let gpaths ← gpaths_ref.get

    IO.println s!"Found {gpaths.size} GPath(s) at step {current_step}\n"

    for (gpath_idx, gpath) in gpaths.toList.mapIdx (fun i g => (i, g)) do
      IO.println s!"GPath {gpath_idx}:"
      let solutions ← read_all_solutions! gpath
      IO.println s!"  Colorings found: {solutions.size}"

      if !solutions.isEmpty then
        IO.println "  Examples:"
        for (idx, solution) in solutions.toList.take 3 |>.mapIdx (fun i s => (i + 1, s)) do
          let coloring := solution_to_coloring solution
          IO.println s!"    {idx}. {coloring}"
        if solutions.size > 3 then
          IO.println s!"    ... ({solutions.size - 3} more)"
      IO.println ""

  IO.println "Execution complete"
