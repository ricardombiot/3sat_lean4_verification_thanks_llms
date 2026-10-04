import AbsSat.SatMachine.ImprovesLoad
import AbsSat.Cnf.ClauseOrder
import AbsSat.Cnf.FrontierDerive
import AbsSat.SatMachine.PureSatMachineIO

/-! `lake exe frontier-derive` — derived clause blocks, measured on `SatMachinePureImproves`.

    frontier-derive <file.cnf>...
    frontier-derive --random <vars> <clauses> <count> [seed]

Four variants per formula: the original order, with derived blocks, `minfront`, and
`minfront` with derived blocks. -/

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (selOfAssign)
open AbsSat.SatMachine.ImprovesLoad
open AbsSat.Cnf.ClauseOrder (byMinFrontier frontierProfile)
open AbsSat.Cnf.FrontierDerive
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves (pureAdvanceW pureRunW)
open AbsSat.SatMachine.PureSatMachineIO (read_cnf)

def oracleLimit : Nat := 12

/-- Per step, the map nodes some satisfying assignment selects. -/
def selTable (φ : Cnf) : Array (List NodeId) := Id.run do
  let sols := (bruteForceSat φ).map toAssign
  let n := (stepCount φ).toNat
  let mut t : Array (List NodeId) := Array.replicate n []
  for k in [0:n] do
    t := t.set! k ((sols.map (fun a => selOfAssign φ a k)).eraseDups)
  return t

structure Walk where
  sat : Bool := false
  /-- States summed over every line. -/
  states : Nat := 0
  /-- States whose key no satisfying assignment selects. -/
  useless : Nat := 0
  /-- First line that is empty. -/
  emptyAt : Option Nat := none
  steps : Nat := 0

def walk (φ : Cnf) : Walk := Id.run do
  let sel := selTable φ
  let steps := (stepCount φ - 1).toNat
  let mut line := pureInit φ
  let mut w : Walk := { steps := steps }
  for k in [0:steps + 1] do
    w := { w with states := w.states + line.length,
                  useless := w.useless + (line.filter (fun kv => !(sel[k]!).contains kv.1)).length }
    if line.isEmpty && w.emptyAt.isNone then w := { w with emptyAt := some k }
    if k < steps then line := pureAdvanceW φ line
  return { w with sat := !line.isEmpty }

structure Total where
  states : Nat := 0
  useless : Nat := 0
  drop : Nat := 0
  passes : Nat := 0
  ms : Nat := 0
  /-- Sum over UNSAT formulas of emptyAt / steps, in per mille. -/
  emptyFrac : Nat := 0
  unsat : Nat := 0
  derived : Nat := 0
  deriving Inhabited

def variant (name : String) (φ0 φ : Cnf) (d : Option Derived) : IO (Total × Bool) := do
  if !Dimacs.wfB φ then
    IO.println s!"    {name}: NOT WELL-FORMED"
    return ({}, false)
  let sameSols := bruteForceSat φ == bruteForceSat φ0
  let refL ← IO.mkRef ([] : PureLine)
  let t0 ← IO.monoNanosNow
  refL.set (pureRunW φ)
  let t1 ← IO.monoNanosNow
  let w := walk φ
  let wk := workW φ
  let (fmax, _) := frontierProfile φ
  let oracle := !(bruteForceSat φ0).isEmpty
  let ok := sameSols && w.sat == oracle
  let emptyStr := match w.emptyAt with | some k => s!"{k}/{w.steps}" | none => "-"
  let (nd, nb, rf, cp) := match d with
    | some x => (x.derived, x.blocks, x.refuted, x.capped)
    | none => (0, 0, false, false)
  IO.println s!"    {name}\tclauses={φ.clauses.length} derived={nd} blocks={nb}{if rf then " refuted" else ""}{if cp then " capped" else ""} frontierMax={fmax} sat={w.sat} sameSolutions={sameSols} emptyAt={emptyStr} states={w.states} useless={w.useless} drop={wk.drop} passes={wk.passes} ms={(t1 - t0) / 1000000}{if ok then "" else "  MISMATCH"}"
  let frac := match w.emptyAt with | some k => k * 1000 / (max w.steps 1) | none => 0
  return ({ states := w.states, useless := w.useless, drop := wk.drop, passes := wk.passes,
            ms := (t1 - t0) / 1000000, emptyFrac := if w.sat then 0 else frac,
            unsat := if w.sat then 0 else 1, derived := nd }, ok)

def names : List String := ["original", "original+derived", "minfront", "minfront+derived"]

def formula (name : String) (φ : Cnf) (tot : Array Total) : IO (Array Total × Bool) := do
  IO.println s!"{name}: vars={φ.nVars} clauses={φ.clauses.length}"
  if φ.nVars > oracleLimit then
    IO.println "    skipped: too many variables for the oracle"
    return (tot, true)
  let cap := 4 * φ.clauses.length
  let mf := byMinFrontier φ
  let d1 := derive φ cap
  let d2 := derive mf cap
  let vs : List (Cnf × Option Derived) := [(φ, none), (d1.cnf, some d1), (mf, none), (d2.cnf, some d2)]
  let mut t := tot
  let mut ok := true
  let mut i := 0
  for (ψ, d) in vs do
    let (r, o) ← variant (names.getD i "") φ ψ d
    ok := ok && o
    let a := t[i]!
    t := t.set! i { states := a.states + r.states, useless := a.useless + r.useless,
                    drop := a.drop + r.drop, passes := a.passes + r.passes, ms := a.ms + r.ms,
                    emptyFrac := a.emptyFrac + r.emptyFrac, unsat := a.unsat + r.unsat,
                    derived := a.derived + r.derived }
    i := i + 1
  return (t, ok)

def main (args : List String) : IO UInt32 := do
  let mut tot : Array Total := Array.replicate 4 {}
  let mut ok := true
  let mut n := 0
  match args with
  | "--random" :: nv :: m :: count :: rest =>
    match nv.toNat?, m.toNat?, count.toNat?, (rest.headD "1").toNat? with
    | some nv, some m, some count, some seed =>
      for i in [0:count] do
        let (t, o) ← formula s!"random n={nv} m={m} seed={seed + i}" (randCnf (seed + i) nv m) tot
        tot := t; ok := ok && o; n := n + 1
    | _, _, _, _ => IO.println "bad arguments"; return 2
  | files =>
    for path in files do
      match ← read_cnf path with
      | .error msg => IO.println s!"{path}: PARSE ERROR {msg}"
      | .ok φ =>
        let (t, o) ← formula path φ tot
        tot := t; ok := ok && o; n := n + 1
  IO.println s!"totals over {n} formulas:"
  for i in [0:4] do
    let a := tot[i]!
    let meanEmpty := if a.unsat == 0 then "-" else s!"{a.emptyFrac / a.unsat}‰"
    IO.println s!"    {names[i]!}\tderived={a.derived} states={a.states} useless={a.useless} drop={a.drop} passes={a.passes} ms={a.ms} unsat={a.unsat} meanEmptyAt={meanEmpty}"
  IO.println (if ok then "ALL OK" else "SOME MISMATCH")
  return if ok then 0 else 1
