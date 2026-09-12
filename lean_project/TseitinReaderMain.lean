import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader.PathReader
open AbsSat.Db.Machine.Cols.ColTimeline

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  LEAN 4: Tseitin Formula Reader Test  ║"
  IO.println "║  (CNF with Tseitin variables)        ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Load CNF
  let cnf_path := "tseitin_test.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found"
    return

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path
  IO.println s!"📋 CNF: {gmap.clausule_counter} clauses"
  IO.println "   Tseitin transformation test\n"

  -- Run machine to completion
  IO.println "🤖 PHASE 1: Running SatMachine"
  let machine ← new gmap
  init! machine
  execute_step! machine

  let found_solution ← have_solution machine
  let current_step ← machine.current_step.get

  IO.println s!"✅ Machine complete: step={current_step}, SAT={found_solution}\n"

  if found_solution then
    -- Extract the final GPath from the timeline
    let timeline ← machine.timeline.get
    let final_step := current_step

    -- Collect first GPath from the timeline
    let first_gpath_ref ← IO.mkRef (none : Option GPath)
    for_each_gpath timeline final_step (fun gpath => do
      let current ← first_gpath_ref.get
      if current.isNone then
        first_gpath_ref.set (some gpath)
    )
    let first_gpath ← first_gpath_ref.get

    match first_gpath with
    | none =>
        IO.println "❌ No GPath found in timeline"
    | some gpath =>
        IO.println "📖 PHASE 2: Reading Solutions"
        IO.println "──────────────────────────────"

        try
          let all_solutions ← read_all_solutions! gpath
          IO.println s!"✅ Solutions extracted: {all_solutions.size}"

          if !all_solutions.isEmpty then
            IO.println "\n📝 All solutions:"
            for (idx, solution) in all_solutions.toList.mapIdx (fun idx sol => (idx + 1, sol)) do
              let vars_str := String.intercalate "" (solution.toList.map (fun b => if b then "1" else "0"))
              IO.println s!"   Solution {idx}: {vars_str}"
        catch e =>
          IO.println s!"⚠️  Reader process: {e}"
  else
    IO.println "❌ No solution found (UNSAT)"

  IO.println "\n══════════════════════════════════════════════════"
  IO.println "Tseitin test complete"
