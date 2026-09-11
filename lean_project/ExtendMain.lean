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
  | "--stale" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    let cap := (rest[4]?.bind (·.toNat?)).getD 20
    AbsSat.GraphPath.Model.ExtendSearch.runRandomStale cases seed nvMin nvSpan cap
  | "--zerosons" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomZero cases seed nvMin nvSpan
  | "--descentin" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphPath.Model.ExtendSearch.runRandomDesc cases seed nvMin nvSpan
  | "--downclosed" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphPath.Model.ExtendSearch.runRandomDown cases seed nvMin nvSpan
  | "--core" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphPath.Model.ExtendSearch.runRandomCore cases seed nvMin nvSpan
  | "--closed" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphPath.Model.ExtendSearch.runRandomClosed cases seed nvMin nvSpan
  | "--sweep" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomSweep cases seed nvMin nvSpan
  | "--pickvalid" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomPick cases seed nvMin nvSpan
  | "--nochoice" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomNoChoice cases seed nvMin nvSpan
  | "--trans" :: rest =>
    for path in rest do
      AbsSat.GraphPath.Model.ExtendSearch.reportTrans path
    return 0
  | "--randomtrans" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomTrans cases seed nvMin nvSpan
  | "--bridge" :: rest =>
    for path in rest do
      AbsSat.GraphPath.Model.ExtendSearch.reportBridge path
    return 0
  | "--randombridge" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomBridge cases seed nvMin nvSpan
  | "--pinnedchain" :: rest =>
    for path in rest do
      AbsSat.GraphPath.Model.ExtendSearch.reportPinnedChain path 20
    return 0
  | "--randompinnedchain" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    let cap := (rest[4]?.bind (·.toNat?)).getD 20
    AbsSat.GraphPath.Model.ExtendSearch.runRandomPinnedChain cases seed nvMin nvSpan cap
  | "--pinned" :: rest =>
    for path in rest do
      AbsSat.GraphPath.Model.ExtendSearch.reportPinned path
    return 0
  | "--randompinned" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 50
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomPinned cases seed nvMin nvSpan
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
  | "--randomclique" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 8
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let budget := (rest[4]?.bind (·.toNat?)).getD 20000
    AbsSat.GraphPath.Model.ExtendSearch.runRandomCQ cases seed nvMin nvSpan budget
  | "--randomgoodparent" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 4
    AbsSat.GraphPath.Model.ExtendSearch.runRandomGP cases seed nvMin nvSpan
  | "--randomdowntop" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 8
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let budget := (rest[4]?.bind (·.toNat?)).getD 20000
    AbsSat.GraphPath.Model.ExtendSearch.runRandomDownTop cases seed nvMin nvSpan budget
  | "--randomhist" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 4
    AbsSat.GraphPath.Model.ExtendSearch.runRandomHist cases seed nvMin nvSpan
  | "--randomsup" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 8
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let budget := (rest[4]?.bind (·.toNat?)).getD 20000
    AbsSat.GraphPath.Model.ExtendSearch.runRandomSup cases seed nvMin nvSpan budget
  | "--randomthread" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 10
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 4
    AbsSat.GraphPath.Model.ExtendSearch.runRandomThread cases seed nvMin nvSpan
  | "--randomsym" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 40
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphPath.Model.ExtendSearch.runRandomSym cases seed nvMin nvSpan
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
