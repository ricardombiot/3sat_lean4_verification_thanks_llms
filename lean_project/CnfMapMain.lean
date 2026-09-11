-- lean_project/CnfMapMain.lean
import AbsSat.GraphMap.CnfMapDiff

/-- `lake exe cnfmap [cases] [seed] [minVars] [varSpan]` — checks the pure
arithmetic map (`CnfMap`) against the map `ImportCnf` actually builds. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--exact" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.CnfMapDiff.runExact cases seed nvMin nvSpan
  | "--driver" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 60
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphMap.CnfMapDiff.runDriver cases seed nvMin nvSpan
  | "--rough" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 100
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 5
    AbsSat.GraphMap.CnfMapDiff.runRough cases seed nvMin nvSpan
  | args =>
  let cases := (args[0]?.bind (·.toNat?)).getD 200
  let seed := (args[1]?.bind (·.toNat?)).getD 2026
  let nvMin := (args[2]?.bind (·.toNat?)).getD 3
  let nvSpan := (args[3]?.bind (·.toNat?)).getD 5
  AbsSat.GraphMap.CnfMapDiff.run cases seed nvMin nvSpan
