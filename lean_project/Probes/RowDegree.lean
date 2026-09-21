import AbsSat.Cnf.Dimacs
import AbsSat.SatMachine.DiffTest
import AbsSat.GraphPath.Model.PureDriverImproves

/-! # The in-degree of the row

Measures `ParentWitness.SingleParents` — *no node has two parents* — which
`Descent.commonOwner_of_singleParents` turns into the whole verdict of route C.
By `ParentWitness.parents_differ_below` two parents of a node agree on their map id and on
their own parent and differ only in the **grandparent**, so the in-degree of a node is
exactly the number of distinct two-step histories that converge on it.

Two numbers per run:

* **real** — the histogram of `n.parents.length` over every node of every state of every
  line. `SingleParents` holds iff the whole mass sits at 1 (step 0 has in-degree 0).
* **w2 vs w3** — the counterfactual. A row node of a window-`w` machine groups the previous
  line by its first `w-1` components, so grouping `g.line (k-1)` by `q.id` alone is what the
  in-degree *would* be with a window of two, and grouping by `(q.id, q.parent_id)` is what it
  is now. The gap between the two is what the third component bought.

Usage: `lake exe row-degree file <cnf>...`
       `lake exe row-degree random <cases> <minVars> <seed>...`
-/

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves

namespace Probes.RowDegree

structure Acc where
  formulas : Nat := 0
  states   : Nat := 0
  nodes    : Nat := 0          -- nodes above step 0
  deg1     : Nat := 0          -- with exactly one parent
  degMore  : Nat := 0          -- with two or more
  degSum   : Nat := 0
  degMax   : Nat := 0
  moreLit  : Nat := 0          -- in-degree ≥2 inside the literal block
  moreCla  : Nat := 0          -- in-degree ≥2 at or above the clause block
  nodesLit : Nat := 0
  nodesCla : Nat := 0
  /-- counterfactual grouping of each line -/
  grp3     : Nat := 0          -- groups under the window of three (= row nodes now)
  grp2     : Nat := 0          -- groups under a window of two
  src      : Nat := 0          -- nodes of the line being grouped
  /-- the worst offender, for a pointer back into the corpus -/
  worstAt  : String := "-"
  deriving Repr

def bump (a : Acc) (d : Nat) (lit : Bool) : Acc :=
  { a with nodes := a.nodes + 1
         , deg1 := a.deg1 + (if d == 1 then 1 else 0)
         , degMore := a.degMore + (if d > 1 then 1 else 0)
         , degSum := a.degSum + d
         , degMax := max a.degMax d
         , nodesLit := a.nodesLit + (if lit then 1 else 0)
         , nodesCla := a.nodesCla + (if lit then 0 else 1)
         , moreLit := a.moreLit + (if d > 1 && lit then 1 else 0)
         , moreCla := a.moreCla + (if d > 1 && !lit then 1 else 0) }

/-- Count the distinct keys of a list, by a projection. -/
def distinctBy {α β : Type} [BEq β] (f : α → β) (l : List α) : Nat :=
  (l.foldl (fun acc x => if acc.contains (f x) then acc else f x :: acc) []).length

def scanState (lb : Int) (label : String) (g : GPathM) (a : Acc) : Acc := Id.run do
  let mut a := { a with states := a.states + 1 }
  -- (1) the real in-degree, node by node
  for n in g.nodes do
    if n.id.id.step > 0 then
      let d := n.parents.length
      if d > a.degMax then
        a := { a with worstAt := s!"{label} step {n.id.id.step} deg {d}" }
      a := bump a d (n.id.id.step < lb)
  -- (2) the counterfactual, line by line
  let mut k : Int := 0
  while k < g.current_step - 1 do
    let ids := (g.line k).map (·.id)
    if !ids.isEmpty then
      a := { a with src := a.src + ids.length
                  , grp2 := a.grp2 + distinctBy (fun q => q.id) ids
                  , grp3 := a.grp3 + distinctBy (fun q => (q.id, q.parent_id)) ids }
    k := k + 1
  return a

/-- Every line of the run, not just the last. -/
def runFormula (φ : Cnf) (a : Acc) : Acc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for i in [0:steps] do
    line := pureAdvanceW φ line
    for kv in line do
      a := scanState (litBlock φ) s!"line {i+1} key ⟨{kv.1.step},{kv.1.index}⟩" kv.2 a
  return a

def report (name : String) (a : Acc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, states {a.states}, nodes above step 0: {a.nodes}"
  IO.println s!"   in-degree 1  : {a.deg1}  ({pct a.deg1 a.nodes})"
  IO.println s!"   in-degree ≥2 : {a.degMore}  ({pct a.degMore a.nodes})   max {a.degMax}"
  if a.nodes > 0 then
    let c := a.degSum * 100 / a.nodes
    IO.println s!"   mean         : {c / 100}.{if c % 100 < 10 then "0" else ""}{c % 100}"
    IO.println s!"   ≥2 literales: {a.moreLit}/{a.nodesLit} ({pct a.moreLit a.nodesLit})   ≥2 clausulas: {a.moreCla}/{a.nodesCla} ({pct a.moreCla a.nodesCla})"
  IO.println s!"   SingleParents: {if a.degMore == 0 then "HOLDS" else "fails"}"
  IO.println s!"   grouping of the previous line: {a.src} ids → {a.grp2} groups (w=2), {a.grp3} groups (w=3)"
  if a.degMore > 0 then IO.println s!"   worst: {a.worstAt}"
  IO.println s!"   ({ms} ms)"

def loadCnf (path : String) : IO (Option Cnf) := do
  let txt ← IO.FS.readFile path
  match AbsSat.Cnf.Dimacs.parse (txt.splitOn "\n") with
  | .error _ => return none
  | .ok φ => return (if AbsSat.Cnf.Dimacs.wfB φ then some φ else none)

def randomCnfs (cases nvMin seed : Nat) : List Cnf := Id.run do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut out : List Cnf := []
  for idx in [0:cases] do
    let (rng1, nv) := rng.below 3
    let nVars := nvMin + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
    rng := rng3
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ => if AbsSat.Cnf.Dimacs.wfB φ then out := out ++ [φ]
  return out

end Probes.RowDegree

open Probes.RowDegree in
def main (args : List String) : IO Unit := do
  match args with
  | "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormula φ {})
        let t1 ← IO.monoMsNow
        report path a (t1 - t0)
  | "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : Acc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormula φ a
      let t1 ← IO.monoMsNow
      report s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | _ =>
    IO.println "usage: row-degree file <cnf>... | row-degree random <cases> <minVars> <seed>..."
