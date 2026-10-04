import AbsSat.SatMachine.ImprovesLoad
import AbsSat.SatMachine.PureSatMachineIO
import AbsSat.Cnf.ClauseOrder
import AbsSat.GraphPath.Model.PureDriverPins
import AbsSat.GraphPath.Model.ConservationFilter

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap (stepCount)
open AbsSat.SatMachine.ImprovesLoad
open AbsSat.SatMachine.PureSatMachineIO (read_cnf)
open AbsSat.Cnf.ClauseOrder (byFrequency byGreedy byMinFrontier weakLinks)
open AbsSat.GraphPath.Model.PureDriverPins (pureRunP)
open AbsSat.GraphPath.Model.ConservationFilter (pureRunSac)

/-- Brute force only while it stays cheap. -/
def oracleLimit : Nat := 16

def ms (t0 t1 : Nat) : Nat := (t1 - t0) / 1000000

/-- Run the three machines on one formula and print one report. Returns `false`
on any disagreement. -/
def check (nsac : Nat) (name : String) (φ : Cnf) : IO Bool := do
  if !Dimacs.wfB φ then
    IO.println s!"{name}: SKIP (not well-formed: repeated literal or variable out of range)"
    return true
  -- each result is stored in a ref before the next timestamp, so it is computed there
  let refB ← IO.mkRef ([] : AbsSat.GraphPath.Model.PureDriver.PureLine)
  let refW ← IO.mkRef ([] : AbsSat.GraphPath.Model.PureDriver.PureLine)
  let refP ← IO.mkRef ([] : AbsSat.GraphPath.Model.PureDriver.PureLine)
  let refS ← IO.mkRef ([] : AbsSat.GraphPath.Model.PureDriver.PureLine)
  let t0 ← IO.monoNanosNow
  refB.set ((AbsSat.SatMachine.PureSatMachine.run_pure φ).timeline.getLastD [])
  let t1 ← IO.monoNanosNow
  refW.set (AbsSat.SatMachine.PureSatMachineImproves.final_line
    (AbsSat.SatMachine.PureSatMachineImproves.run_pure φ))
  let t2 ← IO.monoNanosNow
  refP.set (pureRunP φ)
  let t3 ← IO.monoNanosNow
  refS.set (pureRunSac φ nsac)
  let t4 ← IO.monoNanosNow
  let lastBase ← refB.get
  let lastWeak ← refW.get
  let lastPin ← refP.get
  let lastSac ← refS.get
  let nBase := lastBase.length
  let nWeak := lastWeak.length
  let nPin := lastPin.length
  let satBase := nBase != 0
  let satWeak := nWeak != 0
  let satPin := nPin != 0
  let satSac := lastSac.length != 0
  let oracle : Option Bool :=
    if φ.nVars ≤ oracleLimit then some !(bruteForceSat φ).isEmpty else none
  let sameLine := shape lastBase == shape lastWeak && shape lastBase == shape lastPin
    && shape lastBase == shape lastSac
  let l := load φ nsac
  let oracleOk := match oracle with | some o => o == satBase | none => true
  let ok := satBase == satWeak && satBase == satPin && satBase == satSac && sameLine &&
    l.sameReview && l.samePin && l.sameSac && oracleOk
  let oracleStr := match oracle with | some o => toString o | none => "-"
  IO.println s!"{name}: vars={φ.nVars} clauses={φ.clauses.length} weakLinks={weakLinks φ} sat base/weak/pins/sac({nsac})/oracle={satBase}/{satWeak}/{satPin}/{satSac}/{oracleStr} finalLine={if sameLine then "same" else "DIFF"} sameReview weak/pins/sac={l.sameReview}/{l.samePin}/{l.sameSac} {if ok then "OK" else "MISMATCH"}"
  IO.println s!"    sends={l.sends} (with weak entries {l.weakSends})  weakCut={l.weakCut}  pinCut={l.pinCut} (on sends the base review runs: {l.pinCutValid})  sacCut={l.sacCut} ({l.sacCutValid})"
  IO.println s!"    review passes    base {l.passesBase} -> weak {l.passesWeak} ({pct l.passesBase l.passesWeak}) -> pins {l.passesPin} ({pct l.passesBase l.passesPin}) -> sac {l.passesSac} ({pct l.passesBase l.passesSac})"
  IO.println s!"    review drop      base {l.dropBase} -> weak {l.dropWeak} ({pct l.dropBase l.dropWeak}) -> pins {l.dropPin} ({pct l.dropBase l.dropPin}) -> sac {l.dropSac} ({pct l.dropBase l.dropSac})"
  IO.println s!"    dead pre-review  base {l.deadBase} -> weak {l.deadWeak} -> pins {l.deadPin} -> sac {l.deadSac}"
  IO.println s!"    run time ms      base {ms t0 t1} -> weak {ms t1 t2} -> pins {ms t2 t3} -> sac {ms t3 t4}"
  return ok

def orders (which : String) : List (String × (Cnf → Cnf)) :=
  let all := [("original", id), ("freq", byFrequency), ("greedy", byGreedy),
    ("minfront", byMinFrontier)]
  if which == "all" then all else all.filter (·.1 == which)

def checkOrders (which : String) (nsac : Nat) (name : String) (φ : Cnf) : IO Bool := do
  let mut ok := true
  for (o, f) in orders which do
    let r ← check nsac s!"{name} [{o}]" (f φ)
    ok := ok && r
  return ok

def usage : IO Unit := do
  IO.println "Usage:"
  IO.println "  improves-diff [--order ...] [--sac <passes>] <file.cnf>..."
  IO.println "  improves-diff [--order original|freq|greedy|minfront|all] --random <vars> <clauses> <count> [seed]"

def run (which : String) (nsac : Nat) (args : List String) : IO UInt32 := do
  if (orders which).isEmpty then usage; return 2
  match args with
  | [] => usage; return 2
  | "--random" :: n :: m :: count :: rest =>
    match n.toNat?, m.toNat?, count.toNat?, (rest.headD "1").toNat? with
    | some n, some m, some count, some seed =>
      let mut ok := true
      for i in [0:count] do
        let r ← checkOrders which nsac s!"random n={n} m={m} seed={seed + i}" (randCnf (seed + i) n m)
        ok := ok && r
      IO.println (if ok then "ALL OK" else "SOME MISMATCH")
      return if ok then 0 else 1
    | _, _, _, _ => usage; return 2
  | files =>
    let mut ok := true
    for path in files do
      match ← read_cnf path with
      | .error msg => IO.println s!"{path}: PARSE ERROR {msg}"; ok := false
      | .ok φ =>
        let r ← checkOrders which nsac path φ
        ok := ok && r
    IO.println (if ok then "ALL OK" else "SOME MISMATCH")
    return if ok then 0 else 1

partial def parseArgs (which : String) (nsac : Nat) : List String → IO UInt32
  | "--order" :: w :: rest => parseArgs w nsac rest
  | "--sac" :: n :: rest => parseArgs which (n.toNat!) rest
  | rest => run which nsac rest

def main (args : List String) : IO UInt32 := parseArgs "original" 1 args
