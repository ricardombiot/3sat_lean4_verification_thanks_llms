-- IO wrapper for pure SAT machine with debugging output

import AbsSat.SatMachine.PureSatMachine
import AbsSat.Cnf.Dimacs
import AbsSat.Cnf.Formula
import AbsSat.GraphMap.CnfMap

namespace AbsSat.SatMachine.PureSatMachineIO

open AbsSat.Cnf
open AbsSat.Cnf.Dimacs
open AbsSat.SatMachine.PureSatMachine
open AbsSat.GraphMap.CnfMap

/-- Read and parse a DIMACS CNF file -/
def read_cnf (path : String) : IO (Except String Cnf) := do
  let content ← IO.FS.readFile path
  let lines := (content.splitOn "\n").filter (· ≠ "")
  return Dimacs.parse lines

/-- Execute pure machine with IO debugging output -/
def run_debug (cnf : Cnf) : IO SatMachinePure := do
  let m := init_pure cnf
  IO.println s!"Initialized: step 0, {m.timeline[0]!.length} states"

  -- Main loop: execute steps until completion
  let mut current := m
  let max_steps := (stepCount cnf).toNat

  for _step in [1:max_steps] do
    let final_step := (stepCount cnf).toNat
    if current.current_step >= final_step - 1 then break

    current := step_pure current
    IO.println s!"Step {current.current_step}: {if current.current_step < current.timeline.length then current.timeline[current.current_step]!.length else 0} states"

  return current

/-- Solve a CNF file and report results -/
def solve (path : String) (_verbose : Bool := false) : IO Unit := do
  IO.println s!"Loading {path}..."

  let result ← read_cnf path

  match result with
  | Except.error msg =>
    IO.println s!"Error: {msg}"
  | Except.ok cnf =>
    IO.println s!"Parsed: {cnf.nVars} variables, {cnf.clauses.length} clauses"

    -- Run pure machine
    let start_time ← IO.monoMsNow
    let m ← run_debug cnf
    let end_time ← IO.monoMsNow

    -- Report results
    let count := solution_count m
    let sat := is_satisfiable m
    let elapsed_ms := end_time - start_time

    IO.println ""
    IO.println "================================"
    if sat then
      IO.println s!"SATISFIABLE: {count} solutions found"
    else
      IO.println "UNSATISFIABLE"
    IO.println s!"Time: {elapsed_ms}ms"
    IO.println "================================"

end AbsSat.SatMachine.PureSatMachineIO
