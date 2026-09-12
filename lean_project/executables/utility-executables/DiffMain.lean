-- lean_project/DiffMain.lean
import AbsSat.SatMachine.DiffTest

/--
Randomized differential-testing entry point.

Usage: `lake exe diffTest [cases] [seed]` — defaults: 100 cases, seed 2026.
Exit code 1 on any disagreement between SatMachine+Reader and the
ExhaustiveSolver oracle; failing instances are dumped to
`difftest_failure_<k>.cnf` for reproduction.
-/
def main (args : List String) : IO UInt32 := do
  let cases := (args[0]?.bind (·.toNat?)).getD 100
  let seed := (args[1]?.bind (·.toNat?)).getD 2026
  AbsSat.SatMachine.DiffTest.run_diff_tests cases seed
