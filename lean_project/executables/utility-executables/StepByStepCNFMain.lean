import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphMap.GraphMap
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.Db.Machine.Cols.ColTimeline
open AbsSat.Utils.Alias

/-- Debug output for each step -/
def debug_step! (machine : MSat) (step_num : Nat) : IO Unit := do
  let current_step ← machine.current_step.get
  let timeline ← machine.timeline.get
  let counter := get_counter_graphs_step timeline current_step
  let finished ← is_finished machine
  let have_paths ← have_gpaths_step machine

  IO.println s!"┌─ STEP {step_num} ─────────────────────"
  IO.println s!"│ Current step: {current_step}"
  IO.println s!"│ Counter graphs: {counter}"
  IO.println s!"│ Finished: {finished} | Have paths: {have_paths}"
  IO.println s!"└───────────────────────────────────"

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  LEAN 4: Simple CNF Step-by-Step Trace ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Step 1: Load CNF
  IO.println "📋 PHASE 1: Loading CNF"
  IO.println "─────────────────────────────"

  let cnf_path := "convergence_test.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found."
    return

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path
  IO.println s!"✅ CNF Loaded: step={gmap.step}, clauses={gmap.clausule_counter}\n"

  -- Step 2: Create SatMachine
  IO.println "🤖 PHASE 2: Initializing SatMachine"
  IO.println "──────────────────────────────────"

  let machine ← new gmap
  IO.println "✅ SatMachine created\n"

  debug_step! machine 0

  -- Step 3: Initialize with seed paths
  IO.println "\n🌱 PHASE 3: Initializing seed GPaths"
  IO.println "──────────────────────────────────"

  init! machine
  IO.println "✅ Seeds initialized\n"

  debug_step! machine 1

  -- Step 4: Execute main loop with step tracing (manual unroll)
  IO.println "\n▶️  PHASE 4: Executing machine (step by step)"
  IO.println "───────────────────────────────────────────"

  -- Execute up to 10 steps manually
  let finished1 ← is_finished machine
  let have_paths1 ← have_gpaths_step machine

  if !finished1 && have_paths1 then
    IO.println "\n➤ Iteration 1"
    make_step! machine
    debug_step! machine 2

    let finished2 ← is_finished machine
    let have_paths2 ← have_gpaths_step machine
    if !finished2 && have_paths2 then
      IO.println "\n➤ Iteration 2"
      make_step! machine
      debug_step! machine 3

      let finished3 ← is_finished machine
      let have_paths3 ← have_gpaths_step machine
      if !finished3 && have_paths3 then
        IO.println "\n➤ Iteration 3"
        make_step! machine
        debug_step! machine 4

        let finished4 ← is_finished machine
        let have_paths4 ← have_gpaths_step machine
        if !finished4 && have_paths4 then
          IO.println "\n➤ Iteration 4"
          make_step! machine
          debug_step! machine 5

          let finished5 ← is_finished machine
          let have_paths5 ← have_gpaths_step machine
          if !finished5 && have_paths5 then
            IO.println "\n➤ Iteration 5"
            make_step! machine
            debug_step! machine 6
            IO.println "\n⏸️  (Trace showing first 5 iterations)"
          else
            IO.println "\n⏹️  Machine completed"
        else
          IO.println "\n⏹️  Machine completed"
      else
        IO.println "\n⏹️  Machine completed"
    else
      IO.println "\n⏹️  Machine completed"
  else
    IO.println "No paths to execute"

  -- Step 5: Final results
  IO.println "\n✅ PHASE 5: Final Status"
  IO.println "───────────────────────"

  let finished_final ← is_finished machine
  let found_solution ← have_solution machine

  IO.println s!"Machine finished: {finished_final}"
  IO.println s!"Solution found: {found_solution}"

  if found_solution then
    IO.println "\n🎉 SatMachine successfully found a solution! ✅"
  else
    IO.println "\n❌ No solution found"
