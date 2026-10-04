import AbsSat.SatMachine.ImprovesLoad
import AbsSat.Cnf.ClauseOrder
import AbsSat.SatMachine.PureSatMachineIO

open AbsSat.Cnf
open AbsSat.SatMachine.ImprovesLoad
open AbsSat.Cnf.ClauseOrder
open AbsSat.SatMachine.PureSatMachineIO (read_cnf)

/-! `lake exe order-search` — review work of `SatMachinePureImproves` under several clause orders.

    order-search [--orders a,b,...] <file.cnf>...
    order-search [--orders a,b,...] --random <vars> <clauses> <count> [seed]

Ratios are relative to the first order listed. -/

def allOrders : List (String × (Cnf → Cnf)) :=
  [("original", id), ("freq", byFrequency), ("greedy", byGreedy),
   ("minfront", byMinFrontier), ("local", byLocalSearch byMinFrontier),
   ("local-orig", byLocalSearch id), ("rand1", shuffled 11), ("rand2", shuffled 22),
   ("rand3", shuffled 33)]

/-- Per order: sum of log(drop / reference drop), and wins. -/
abbrev Tally := List (String × Float × Nat)

def report (orders : List (String × (Cnf → Cnf))) (name : String) (φ : Cnf) (tally : Tally) :
    IO (Tally × Bool) := do
  let rows := orders.map (fun (o, f) => let ψ := f φ; (o, frontierProfile ψ, workW ψ))
  let base := (rows.headD ("", (0, 0), {})).2.2
  let best := rows.foldl (fun b r => if r.2.2.drop < b then r.2.2.drop else b) base.drop
  let sameSat := rows.all (fun r => r.2.2.sat == base.sat)
  IO.println s!"{name}: vars={φ.nVars} clauses={φ.clauses.length} sat={base.sat}{if sameSat then "" else " VERDICT MISMATCH"}"
  let mut t := tally
  for (o, (fmax, fsum), w) in rows do
    let ratio : Float := if base.drop == 0 then 1.0 else w.drop.toFloat / base.drop.toFloat
    IO.println s!"    {o}\tfrontier max={fmax} sum={fsum}\tdrop={w.drop}\tpasses={w.passes}\tmass={w.mass}\tx{ratio}{if w.drop == best then "  <- best" else ""}"
    t := t.map (fun e => if e.1 == o then (o, e.2.1 + Float.log (max ratio 1e-9), e.2.2 + (if w.drop == best then 1 else 0)) else e)
  return (t, sameSat)

def main (args : List String) : IO UInt32 := do
  let sel : List (String × (Cnf → Cnf)) × List String := match args with
    | "--orders" :: names :: rest =>
      let wanted := names.splitOn ","
      (wanted.filterMap (fun w => allOrders.find? (fun (e : String × (Cnf → Cnf)) => e.1 == w)), rest)
    | _ => (allOrders, args)
  let orders := sel.1
  let args := sel.2
  if orders.isEmpty then IO.println "no known order selected"; return 2
  let mut tally : Tally := orders.map (fun (o : String × (Cnf → Cnf)) => (o.1, 0.0, 0))
  let mut n : Nat := 0
  let mut ok := true
  match args with
  | "--random" :: nv :: m :: count :: rest =>
    match nv.toNat?, m.toNat?, count.toNat?, (rest.headD "1").toNat? with
    | some nv, some m, some count, some seed =>
      for i in [0:count] do
        let (t, s) ← report orders s!"random n={nv} m={m} seed={seed + i}" (randCnf (seed + i) nv m) tally
        tally := t; ok := ok && s; n := n + 1
    | _, _, _, _ => IO.println "bad arguments"; return 2
  | files =>
    for path in files do
      match ← read_cnf path with
      | .error msg => IO.println s!"{path}: PARSE ERROR {msg}"
      | .ok φ =>
        let (t, s) ← report orders path φ tally
        tally := t; ok := ok && s; n := n + 1
  IO.println s!"summary over {n} formulas (geometric mean of drop relative to {(orders.headD ("", id)).1}, wins):"
  for (o, lsum, wins) in tally do
    IO.println s!"    {o}\tx{Float.exp (lsum / n.toFloat)}\twins={wins}"
  return if ok then 0 else 1
