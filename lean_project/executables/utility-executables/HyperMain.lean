-- lean_project/HyperMain.lean
import AbsSat.GraphMap.HyperProbe

/-- Measures α-acyclicity of the constraint hypergraph of the 3SAT maps.

    lake exe hyper <file.cnf> ...
    lake exe hyper --random <cases> <seed> [minVars] [varSpan] -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "usage: lake exe hyper <file.cnf> ...\n\
                       lake exe hyper --random <cases> <seed> [minVars] [varSpan]"
    return 1
  | "--random" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphMap.HyperProbe.runRandom cases seed nvMin nvSpan
  | paths =>
    for path in paths do
      let _ ← AbsSat.GraphMap.HyperProbe.report path
    return 0
