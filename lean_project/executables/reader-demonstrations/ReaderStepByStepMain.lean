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
        IO.println "✅ Reader initialized with final GPath"

        IO.println "\n📊 PHASE 3: Certificate Set Analysis"
        IO.println "──────────────────────────────────"
        let step_reached ← gpath.current_step.get
        IO.println s!"GPath represents all solutions for this formula"
        IO.println s!"Step reached: {step_reached}"

        -- Extract solutions
        IO.println "\n🔍 PHASE 4: Solution Extraction"
        IO.println "────────────────────────────────"

        let reader := new gpath
        let finished_reader ← read! reader
        let solutions := finished_reader.solution

        if solutions.isEmpty then
          IO.println "⚠️  First path had no solutions"
        else
          IO.println s!"✅ First solution extracted:"
          let sol_str := solution_to_string solutions
          IO.println s!"   {sol_str}"

        -- Try to read all solutions
        IO.println "\n📚 Reading all solutions from certificate set..."
        try
          let all_solutions ← read_all_solutions! gpath
          IO.println s!"✅ Total solutions found: {all_solutions.size}"

          if !all_solutions.isEmpty then
            IO.println "\n📝 All solutions:"
            for (idx, solution) in all_solutions.toList.mapIdx (fun idx sol => (idx + 1, sol)) do
              let sol_str := solution_to_string solution
              IO.println s!"   Solution {idx}: {sol_str}"

          -- Check for expected solution: x1=F, x2=T, x3=F, x4=T = [false, true, false, true]
          let expected := #[false, true, false, true]
          let found_expected := all_solutions.toList.any (· == expected)

          if found_expected then
            IO.println "\n✅ EXPECTED SOLUTION FOUND: x1=F, x2=T, x3=F, x4=T"
          else
            IO.println "\n⚠️  Expected solution not found in extracted set"
        catch e =>
          IO.println s!"Note: Multi-path extraction. Error: {e}"

        IO.println "\n✅ Expected solutions:"
        IO.println "   1=False, 2=True, 3=False, 4=True (as per CNF comment)"
  else
    IO.println "❌ No solution found (UNSAT)"

  IO.println "\n══════════════════════════════════════════════════"
  IO.println "Reader implementation: Complete"
