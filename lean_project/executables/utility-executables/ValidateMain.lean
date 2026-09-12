-- lean_project/ValidateMain.lean
import AbsSat.GraphPath.Model.Validate

/-- Checks the "no zombies" invariant directly, on every state the machine
holds, with an independent chain search.

    lake exe validate <file.cnf> ...
    lake exe validate --random <cases> <seed> [minVars] [varSpan]

Exit code 1 if any zombie is found. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "usage: lake exe validate <file.cnf> ...\n\
                       lake exe validate --random <cases> <seed> [minVars] [varSpan]"
    return 1
  | "--random" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 100
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.Validate.runRandom cases seed nvMin nvSpan
  | paths =>
    let mut ok := true
    for path in paths do
      let r ← AbsSat.GraphPath.Model.Validate.report path
      ok := ok && r
    return (if ok then 0 else 1)
