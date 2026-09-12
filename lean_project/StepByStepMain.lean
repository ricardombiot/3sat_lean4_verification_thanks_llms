import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.GraphMap
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.Db.Machine.Cols.ColTimeline
open AbsSat.Utils.Alias

/-- Simple step-by-step execution to see Timeline state evolution -/
def debug_step! (machine : MSat) (step_num : Nat) : IO Unit := do
  let current_step ← machine.current_step.get
  let timeline ← machine.timeline.get
  let counter := get_counter_graphs_step timeline current_step
  let finished ← is_finished machine
  let have_paths ← have_gpaths_step machine

  IO.println s!"┌─ STEP {step_num} ─────────────────────"
  IO.println s!"│ Current step: {current_step}"
  IO.println s!"│ Counter graphs at step: {counter}"
  IO.println s!"│ Machine finished: {finished}"
  IO.println s!"│ Have paths: {have_paths}"
  IO.println s!"└───────────────────────────────────"

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  LEAN 4 SatMachine Step-by-Step Trace  ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Step 1: Create a simple GraphMap
  IO.println "📋 PHASE 1: Creating GraphMap"
  IO.println "─────────────────────────────"

  let gmap ← GraphMap.new
  IO.println s!"GMap created: step={gmap.step}, clauses={gmap.clausule_counter}\n"

  -- Step 2: Create SatMachine
  IO.println "🤖 PHASE 2: Initializing SatMachine"
  IO.println "──────────────────────────────────"

  let machine ← new gmap
  IO.println "SatMachine created\n"

  debug_step! machine 0

  -- Step 3: Initialize with seed paths
  IO.println "\n🌱 PHASE 3: Initializing seed GPaths"
  IO.println "──────────────────────────────────"

  init! machine
  IO.println "Seeds initialized\n"

  debug_step! machine 1

  -- Step 4: Execute main loop with tracing
  IO.println "\n▶️  PHASE 4: Executing machine (step by step)"
  IO.println "───────────────────────────────────────────"

  let finished_initial ← is_finished machine
  let have_paths_initial ← have_gpaths_step machine

  if !finished_initial && have_paths_initial then
    -- Do first step manually
    IO.println "\n➤ Executing make_step! #1"
    make_step! machine
    debug_step! machine 2

    -- Do second step
    let finished2 ← is_finished machine
    let have_paths2 ← have_gpaths_step machine
    if !finished2 && have_paths2 then
      IO.println "\n➤ Executing make_step! #2"
      make_step! machine
      debug_step! machine 3

      -- Do third step
      let finished3 ← is_finished machine
      let have_paths3 ← have_gpaths_step machine
      if !finished3 && have_paths3 then
        IO.println "\n➤ Executing make_step! #3"
        make_step! machine
        debug_step! machine 4

        IO.println "\n⏸️  (trace limited to 3 steps for clarity)"
      else
        IO.println "\n⏹️  Machine stopped after step 2"
    else
      IO.println "\n⏹️  Machine stopped after step 1"
  else
    IO.println "No paths to execute (empty GraphMap)"

  -- Step 5: Final results
  IO.println "\n✅ PHASE 5: Final Status"
  IO.println "───────────────────────"

  let finished_final ← is_finished machine
  let found_solution ← have_solution machine

  IO.println s!"Machine finished: {finished_final}"
  IO.println s!"Solution found: {found_solution}"

  if found_solution then
    IO.println "\n🎉 SatMachine successfully found a solution!"
  else
    IO.println "\n❌ No solution found (or GraphMap empty)"
