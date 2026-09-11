-- lean_project/CnfMapMain.lean
import AbsSat.GraphMap.CnfMapDiff
import AbsSat.GraphMap.SymCampaign

/-- `lake exe cnfmap [cases] [seed] [minVars] [varSpan]` — checks the pure
arithmetic map (`CnfMap`) against the map `ImportCnf` actually builds. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--insert" :: rest =>
    let lo := (rest[0]?.bind (·.toNat?)).getD 3
    let hi := (rest[1]?.bind (·.toNat?)).getD 7
    AbsSat.GraphMap.SymCampaign.runInsert lo hi
  | "--tseitin" :: rest =>
    let perms := (rest[0]?.bind (·.toNat?)).getD 5
    let seed := (rest[1]?.bind (·.toNat?)).getD 1
    let maxG := (rest[2]?.bind (·.toNat?)).getD 5
    AbsSat.GraphMap.SymCampaign.runTseitin perms seed maxG
  | "--hunt" :: rest =>
    let trials := (rest[0]?.bind (·.toNat?)).getD 200
    let maxExtra := (rest[1]?.bind (·.toNat?)).getD 4
    let seed := (rest[2]?.bind (·.toNat?)).getD 1
    AbsSat.GraphMap.SymCampaign.runHunt trials maxExtra seed
  | "--exactdiag" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runExactDiag cases seed nvMin nvSpan
  | "--tableexact" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runTableExact cases seed nvMin nvSpan
  | "--fabric" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runFabric cases seed nvMin nvSpan
  | "--selfsupport" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runSelfSupport cases seed nvMin nvSpan
  | "--pinexact" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runPinExact cases seed nvMin nvSpan
  | "--triangle" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runTriangle cases seed nvMin nvSpan
  | "--symreview" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runSymReview cases seed nvMin nvSpan
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
