import AbsSat.SatMachine.ImprovesLoad
import AbsSat.SatMachine.PureSatMachineIO
import AbsSat.Cnf.ClauseOrder

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap (stepCount)
open AbsSat.SatMachine.ImprovesLoad
open AbsSat.SatMachine.PureSatMachineIO (read_cnf)
open AbsSat.Cnf.ClauseOrder (byFrequency byGreedy weakLinks)

/-- Brute force only while it stays cheap. -/
def oracleLimit : Nat := 16

/-- Run both machines on one formula and print one report. Returns `false` on
any disagreement. -/
def check (name : String) (φ : Cnf) : IO Bool := do
  if !Dimacs.wfB φ then
    IO.println s!"{name}: SKIP (not well-formed: repeated literal or variable out of range)"
    return true
  let base := AbsSat.SatMachine.PureSatMachine.run_pure φ
  let weak := AbsSat.SatMachine.PureSatMachineImproves.run_pure φ
  let satBase := AbsSat.SatMachine.PureSatMachine.is_satisfiable base
  let satWeak := AbsSat.SatMachine.PureSatMachineImproves.is_satisfiable weak
  let lastBase := base.timeline.getLastD []
  let lastWeak := AbsSat.SatMachine.PureSatMachineImproves.final_line weak
  let oracle : Option Bool :=
    if φ.nVars ≤ oracleLimit then some !(bruteForceSat φ).isEmpty else none
  let sameLine := shape lastBase == shape lastWeak
  let l := load φ
  let oracleOk := match oracle with | some o => o == satBase | none => true
  let ok := satBase == satWeak && sameLine && l.sameReview && oracleOk
  let oracleStr := match oracle with | some o => toString o | none => "-"
  IO.println s!"{name}: vars={φ.nVars} clauses={φ.clauses.length} weakLinks={weakLinks φ} sat base/improves/oracle={satBase}/{satWeak}/{oracleStr} finalLine={if sameLine then "same" else "DIFF"} {if ok then "OK" else "MISMATCH"}"
  IO.println s!"    sends={l.sends} (with weak entries {l.weakSends})  weakCut={l.weakCut}"
  IO.println s!"    review passes    {l.passesBase} -> {l.passesWeak} ({pct l.passesBase l.passesWeak})"
  IO.println s!"    review drop      {l.dropBase} -> {l.dropWeak} ({pct l.dropBase l.dropWeak})"
  IO.println s!"    dead pre-review  {l.deadBase} -> {l.deadWeak}"
  return ok

def orders (which : String) : List (String × (Cnf → Cnf)) :=
  let all := [("original", id), ("freq", byFrequency), ("greedy", byGreedy)]
  if which == "all" then all else all.filter (·.1 == which)

def checkOrders (which : String) (name : String) (φ : Cnf) : IO Bool := do
  let mut ok := true
  for (o, f) in orders which do
    let r ← check s!"{name} [{o}]" (f φ)
    ok := ok && r
  return ok

def usage : IO Unit := do
  IO.println "Usage:"
  IO.println "  improves-diff [--order original|freq|greedy|all] <file.cnf>..."
  IO.println "  improves-diff [--order original|freq|greedy|all] --random <vars> <clauses> <count> [seed]"

def run (which : String) (args : List String) : IO UInt32 := do
  if (orders which).isEmpty then usage; return 2
  match args with
  | [] => usage; return 2
  | "--random" :: n :: m :: count :: rest =>
    match n.toNat?, m.toNat?, count.toNat?, (rest.headD "1").toNat? with
    | some n, some m, some count, some seed =>
      let mut ok := true
      for i in [0:count] do
        let r ← checkOrders which s!"random n={n} m={m} seed={seed + i}" (randCnf (seed + i) n m)
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
        let r ← checkOrders which path φ
        ok := ok && r
    IO.println (if ok then "ALL OK" else "SOME MISMATCH")
    return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "--order" :: which :: rest => run which rest
  | _ => run "original" args
