-- Validation: Test PureSatMachine on documented test cases

import AbsSat.SatMachine.PureSatMachine
import AbsSat.SatMachine.PureSatMachineIO
import AbsSat.Cnf.Dimacs

open AbsSat.Cnf
open AbsSat.Cnf.Dimacs
open AbsSat.SatMachine.PureSatMachine
open AbsSat.SatMachine.PureSatMachineIO

/-- Validate pure machine on a CNF file -/
def validate_cnf (path : String) (expected_final_states : Nat) : IO Unit := do
  IO.println s!"Validating {path}..."

  -- Load and parse CNF
  let result ← read_cnf path
  match result with
  | Except.error msg =>
    IO.println s!"ERROR parsing: {msg}"
  | Except.ok cnf =>
    -- Run pure machine
    let pure_result := run_pure cnf
    let pure_final_states := if pure_result.timeline.isEmpty then 0 else pure_result.timeline[pure_result.timeline.length - 1]!.length
    let pure_sat := is_satisfiable pure_result

    IO.println s!"Pure Machine Results:"
    IO.println s!"  Final states: {pure_final_states}"
    IO.println s!"  Satisfiable: {pure_sat}"
    IO.println s!"  Expected: {expected_final_states} states"

    if pure_final_states = expected_final_states then
      IO.println s!"  ✓ PASS"
    else
      IO.println s!"  ✗ FAIL: Expected {expected_final_states}, got {pure_final_states}"

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    IO.println "Pure SAT Machine Validator"
    IO.println "Usage: diff-pure-msat <test-name>"
    IO.println ""
    IO.println "Available tests:"
    IO.println "  test_sat_medium"
    IO.println "  tseitin"
    IO.println "  pigeonhole"
    IO.println "  graph_coloring"
  | ["test_sat_medium"] =>
    validate_cnf "test/cnf/satisfiable/simple/test_sat_medium.cnf" 9
  | ["tseitin"] =>
    validate_cnf "test/cnf/satisfiable/tseitin/tseitin_correct.cnf" 2
  | ["pigeonhole"] =>
    validate_cnf "test/cnf/unsatisfiable/pigeonhole/pigeonhole.cnf" 0
  | ["graph_coloring"] =>
    validate_cnf "test/cnf/satisfiable/graph-coloring/graph_coloring_3col.cnf" 12
  | [file] =>
    validate_cnf file 0
  | _ =>
    IO.println "Invalid arguments"
