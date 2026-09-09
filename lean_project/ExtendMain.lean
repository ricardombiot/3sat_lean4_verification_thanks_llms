-- lean_project/ExtendMain.lean
import AbsSat.GraphPath.Model.ExtendSearch

/-- Falsifier for route A: is the machine's state backtrack-free?

    lake exe extend <file.cnf> ...
    lake exe extend --random <cases> <seed> [minVars] [varSpan] [budget]

Exit code 1 if a consistent partial chain is found with no continuation. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "usage: lake exe extend <file.cnf> ...\n\
                       lake exe extend --random <cases> <seed> [minVars] [varSpan] [budget]\n\
                       lake exe extend --syn <steps> <width> <trials> [budget]"
    return 1
  | "--reqpaths" :: rest =>
    for path in rest do
      AbsSat.GraphPath.Model.ExtendSearch.reportReqPaths path 300
    return 0
  | "--randomreqpaths" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    let cap := (rest[4]?.bind (·.toNat?)).getD 300
    AbsSat.GraphPath.Model.ExtendSearch.runRandomReqPaths cases seed nvMin nvSpan cap
  | "--owners" :: rest =>
    for path in rest do
      AbsSat.GraphPath.Model.ExtendSearch.reportOwners path
    return 0
  | "--randomowners" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomOwners cases seed nvMin nvSpan
  | "--descend" :: rest =>
    let mut ok := true
    for path in rest do
      let r ← AbsSat.GraphPath.Model.ExtendSearch.reportDescend path
      ok := ok && r
    return (if ok then 0 else 1)
  | "--randomdescend" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomDescend cases seed nvMin nvSpan
  | "--randomread" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    let budget := (rest[4]?.bind (·.toNat?)).getD 20000
    AbsSat.GraphPath.Model.ExtendSearch.runRandomRead cases seed nvMin nvSpan budget
  | "--read" :: rest =>
    let mut ok := true
    for path in rest do
      let r ← AbsSat.GraphPath.Model.ExtendSearch.reportRead path 20000
      ok := ok && r
    return (if ok then 0 else 1)
  | "--syn" :: rest =>
    let steps := (rest[0]?.bind (·.toNat?)).getD 6
    let width := (rest[1]?.bind (·.toNat?)).getD 3
    let trials := (rest[2]?.bind (·.toNat?)).getD 60
    let budget := (rest[3]?.bind (·.toNat?)).getD 20000
    AbsSat.GraphPath.Model.ExtendSearch.runSynthetic steps width trials budget
  | "--random" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    let budget := (rest[4]?.bind (·.toNat?)).getD 20000
    AbsSat.GraphPath.Model.ExtendSearch.runRandom cases seed nvMin nvSpan budget
  | paths =>
    let mut ok := true
    for path in paths do
      let r ← AbsSat.GraphPath.Model.ExtendSearch.report path 20000
      ok := ok && r
    return (if ok then 0 else 1)
