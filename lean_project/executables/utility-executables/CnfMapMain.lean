-- lean_project/CnfMapMain.lean
import AbsSat.GraphMap.CnfMapDiff
import AbsSat.GraphMap.SymCampaign

/-- `lake exe cnfmap [cases] [seed] [minVars] [varSpan]` — checks the pure
arithmetic map (`CnfMap`) against the map `ImportCnf` actually builds. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--insertgen" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runInsertGen (g 0 2026) (g 1 5) (g 2 2) (g 3 4) (g 4 2) (g 5 3)
      ((rest[6]?.getD "tri") == "tri")
  | "--joined" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runJoined cases seed nvMin nvSpan
  | "--p4narrow" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let mode := (rest[4]?).getD "orig"
    AbsSat.GraphMap.SymCampaign.runP4Narrow cases seed nvMin nvSpan mode
  | "--p4why" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let mode := (rest[4]?).getD "orig"
    AbsSat.GraphMap.SymCampaign.runP4Why cases seed nvMin nvSpan mode
  | "--p4clause" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let mode := (rest[4]?).getD "orig"
    AbsSat.GraphMap.SymCampaign.runP4Clause cases seed nvMin nvSpan mode
  | "--p3" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runP3 (g 0 10) (g 1 2026) (g 2 3) (g 3 3)
  | "--tauto" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runTauto (g 0 10) (g 1 2026) (g 2 3) (g 3 3)
  | "--fabclause" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runFabricClause (g 0 15) (g 1 2026) (g 2 3) (g 3 3)
  | "--band" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runBand (g 0 40) (g 1 2026) (g 2 3) (g 3 4) (g 4 4)
  | "--pickstep" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runPickStep (g 0 60) (g 1 2026) (g 2 3) (g 3 4) (g 4 4)
  | "--reducer" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runReducer (g 0 60) (g 1 2026) (g 2 3) (g 3 4) (g 4 4)
  | "--flipscope" :: rest =>
    let g := fun (i : Nat) (d : Nat) => (rest[i]?.bind (·.toNat?)).getD d
    AbsSat.GraphMap.SymCampaign.runFlipScope (g 0 40) (g 1 2026) (g 2 3) (g 3 3) (g 4 8) (g 5 2)
      (g 6 4)
  | "--triples" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    let samples := (rest[4]?.bind (·.toNat?)).getD 300
    AbsSat.GraphMap.SymCampaign.runTriples cases seed nvMin nvSpan samples
  | "--tri" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runTri cases seed nvMin nvSpan
  | "--case17" :: _ => AbsSat.GraphMap.SymCampaign.runCase17
  | "--flipcases" :: rest =>
    let cases := (rest[0]?.bind (·.toNat?)).getD 20
    let seed := (rest[1]?.bind (·.toNat?)).getD 2026
    let nvMin := (rest[2]?.bind (·.toNat?)).getD 3
    let nvSpan := (rest[3]?.bind (·.toNat?)).getD 3
    AbsSat.GraphMap.SymCampaign.runFlipCases cases seed nvMin nvSpan
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
