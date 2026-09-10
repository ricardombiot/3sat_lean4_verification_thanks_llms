-- lean_project/AbsSat/GraphMap/CnfMapDiff.lean
import AbsSat.GraphMap.CnfMap
import AbsSat.GraphMap.CnfSel
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.Cnf.Dimacs
import AbsSat.GraphMap.ImportCnf
import AbsSat.SatMachine.DiffTest

/-!
# `lake exe cnfmap` — the arithmetic map against the real one

`CnfMap.reqOfCnf` and `CnfMap.mapNodes` claim to reproduce what
`GraphMap.add_var!` / `add_gate_case!` / `make_fusion_node!` build. Every
theorem downstream is a correct proof about the *wrong map* if that claim is
off by one anywhere — the fusion node's step, the `2n+1+j` offset, the
bit-to-position mapping, the `1 - index` of the negation block — and the axiom
pins would certify it happily.

So this band hands the same DIMACS text to both sides and compares, per step
and per node:

* `CnfMap.stepCount φ` against `gmap.step`;
* `CnfMap.mapNodes φ k` against `get_ids_step gmap k`;
* `CnfMap.reqOfCnf φ d` against the requirements the real node carries.

**Three outcomes, not two.** A clause that repeats a literal of the same
polarity cannot be represented (`MapReqs.repeated_literal_not_functional`), so
such an instance is **skipped**, counted separately, and never reported as
agreement. Requirements are compared as *sorted* key lists, because
`MapDocNode.requires` is a `HashSet` and enumerates in hash order.

This file is `IO`, has no theorems and no axiom pins, so its use of Std's
classical `HashSet` lemmas cannot contaminate anything.
-/

namespace AbsSat.GraphMap.CnfMapDiff

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap
open AbsSat.GraphMap.GraphMap
open AbsSat.GraphMap.ImportCnf
open AbsSat.GraphMap.CnfMap

/-- The requirements the executable's map actually carries, as `ExtendSearch`
reads them. -/
def reqOfG (gmap : GMap) (d : NodeId) : List NodeId :=
  match get_node gmap d with
  | some n => n.requires.toList
  | none => []

/-- The sons the executable's map actually carries. -/
def sonsOfG (gmap : GMap) (d : NodeId) : List NodeId :=
  match get_node gmap d with
  | some n => n.sons.toList
  | none => []

def sortedKeys (ids : List NodeId) : List String :=
  ((ids.map as_key).toArray.qsort (fun a b => decide (a < b))).toList

/-- `(cases, agreed, disagreed, skipped)` -/
abbrev DAcc := Nat × Nat × Nat × Nat

structure Report where
  ok : Bool
  msg : String

def compareMap (φ : Cnf) (gmap : GMap) : Report := Id.run do
  let sc := stepCount φ
  if sc != gmap.step then
    let m := "stepCount " ++ toString sc ++ " vs gmap.step " ++ toString gmap.step
    return { ok := false, msg := m }
  if φ.clauses.length != gmap.clausule_counter then
    let m := "clauses " ++ toString φ.clauses.length
      ++ " vs counter " ++ toString gmap.clausule_counter
    return { ok := false, msg := m }
  let mut bad : Option String := none
  for k in (List.range gmap.step.toNat) do
    let kk : Int := (k : Int)
    let mine := sortedKeys (mapNodes φ kk)
    let theirs := sortedKeys (get_ids_step gmap kk).toList
    if mine != theirs then
      if bad.isNone then
        bad := some ("step " ++ toString kk ++ ": nodes " ++ toString mine
          ++ " vs " ++ toString theirs)
    else
      for d in (get_ids_step gmap kk).toList do
        let rmine := sortedKeys (reqOfCnf φ d)
        let rtheirs := sortedKeys (reqOfG gmap d)
        if rmine != rtheirs then
          if bad.isNone then
            bad := some ("node " ++ as_key d ++ ": reqs " ++ toString rmine
              ++ " vs " ++ toString rtheirs)
        let smine := sortedKeys (CnfSel.mapSons φ kk d.index)
        let stheirs := sortedKeys (sonsOfG gmap d)
        if smine != stheirs then
          if bad.isNone then
            bad := some ("node " ++ as_key d ++ ": sons " ++ toString smine
              ++ " vs " ++ toString stheirs)
  match bad with
  | some m => return { ok := false, msg := m }
  | none => return { ok := true, msg := "" }

def runOne (cnf : String) (path : String) : IO (Bool × Bool × String) := do
  IO.FS.writeFile path cnf
  let gmap ← load_import! path
  match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
  | .error e => return (false, false, s!"parser: {e}")
  | .ok φ =>
    if !AbsSat.Cnf.Dimacs.wfB φ then
      return (true, true, "")          -- skipped, not well formed
    else
      let r := compareMap φ gmap
      return (false, r.ok, r.msg)

def run (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- arithmetic map vs the real one: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : DAcc := (0, 0, 0, 0)
  let mut firstFail : Option String := none
  for idx in [0:cases] do
    let (rng1, nv) := rng.below nvSpan
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
    let (skipped, ok, msg) ← runOne cnf "cnfmap_tmp.cnf"
    if skipped then
      acc := (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2 + 1)
    else if ok then
      acc := (acc.1 + 1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
    else
      acc := (acc.1 + 1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2)
      if firstFail.isNone then firstFail := some s!"case {idx}: {msg}\n{cnf}"
  IO.println s!"  cases      = {acc.1}"
  IO.println s!"  agreed     = {acc.2.1}"
  IO.println s!"  DISAGREED  = {acc.2.2.1}"
  IO.println s!"  skipped (not well formed) = {acc.2.2.2}"
  match firstFail with
  | some m => IO.println s!"\nfirst disagreement:\n{m}"; return 1
  | none =>
    IO.println "Arithmetic map matches the built map. ✅"
    return 0

-- ============================================================
-- Malformed instances: the "skipped" path, exercised on purpose
-- ============================================================

/-!
`DiffTest.gen_clause` picks three **distinct** variables, so the normal band
never produces a clause the encoding cannot represent and the skip counter
stays at zero — which would leave the honesty machinery untested. These
generators produce the three ways a DIMACS line goes wrong, with the outcome
each should have:

* **a repeated literal of the same polarity** — the encoding genuinely cannot
  represent it (`MapReqs.repeated_literal_not_functional`), so the instance is
  **skipped**;
* **a literal outside `1..nVars`** — `get_step_var` returns `none` and
  `add_gate!` drops the clause, and the pure parser drops it too, so the two
  sides must still **agree**;
* **a two-literal line** — dropped by both for the same reason, so again
  **agree**.

A skip is never an agreement, and a disagreement here is a real bug in either
the parser or the arithmetic.
-/

def gen_clause_rough (rng : AbsSat.SatMachine.DiffTest.Rng) (nVars : Nat) :
    AbsSat.SatMachine.DiffTest.Rng × String :=
  let (rng, mode) := rng.below 3
  let (rng, a) := rng.below nVars
  let (rng, b) := rng.below nVars
  let va := a + 1
  let vb := b + 1
  if mode == 0 then
    (rng, s!"{va} {va} {vb} 0")            -- repeated, same polarity → skipped
  else if mode == 1 then
    (rng, s!"{nVars + 1} {va} {vb} 0")     -- out of range → dropped by both
  else
    (rng, s!"{va} {vb} 0")                 -- too short → dropped by both

def gen_cnf_rough (rng : AbsSat.SatMachine.DiffTest.Rng) (nVars nClauses : Nat) :
    AbsSat.SatMachine.DiffTest.Rng × String :=
  let (rng, body) := (List.range nClauses).foldl (fun st _ =>
    let (rng, acc) := st
    let (rng, clause) := gen_clause_rough rng nVars
    (rng, acc ++ clause ++ "\n")) (rng, "")
  (rng, s!"p cnf {nVars} {nClauses}\n" ++ body)

def runRough (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- malformed instances: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : DAcc := (0, 0, 0, 0)
  let mut firstFail : Option String := none
  for idx in [0:cases] do
    let (rng1, nv) := rng.below nvSpan
    let nVars := nvMin + nv
    let (rng2, nc) := rng1.below (3 * nVars)
    let (rng3, cnf) := gen_cnf_rough rng2 nVars (1 + nc)
    rng := rng3
    let (skipped, ok, msg) ← runOne cnf "cnfmap_tmp.cnf"
    if skipped then
      acc := (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2 + 1)
    else if ok then
      acc := (acc.1 + 1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
    else
      acc := (acc.1 + 1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2)
      if firstFail.isNone then firstFail := some s!"case {idx}: {msg}\n{cnf}"
  IO.println s!"  cases      = {acc.1}"
  IO.println s!"  agreed     = {acc.2.1}"
  IO.println s!"  DISAGREED  = {acc.2.2.1}"
  IO.println s!"  skipped (not well formed) = {acc.2.2.2}"
  match firstFail with
  | some m => IO.println s!"\nfirst disagreement:\n{m}"; return 1
  | none =>
    if acc.2.2.2 == 0 then
      IO.println "No instance was skipped — the skip path went untested. ⚠"
      return 1
    else
      IO.println "Malformed instances handled: skips counted, no disagreement. ✅"
      return 0

-- ============================================================
-- The pure driver against the real one
-- ============================================================

/-!
`PureDriver.pureRun` is the timeline loop over the arithmetic map;
`MirrorTest.mirrorRun` is the same loop over the `GMap` the importer builds.
This compares them: the set of keys the final line carries, and per key the
node count and the validity of the state parked there.

Titles are not compared. The real driver copies the map node's title into the
graph and the model passes `""`; nothing in `isValid`, `owners` or `denot`
reads it, so a title difference is not a disagreement.
-/

def driverReport (φ : Cnf) (gmap : GMap) : Report := Id.run do
  let mine := AbsSat.GraphPath.Model.PureDriver.pureRun φ
  let theirs := AbsSat.GraphPath.Model.MirrorTest.mirrorRun gmap
  let mk := sortedKeys (mine.map (·.1))
  let tk := sortedKeys (theirs.map (·.1))
  if mk != tk then
    return { ok := false, msg := "driver keys " ++ toString mk ++ " vs " ++ toString tk }
  let mut bad : Option String := none
  for kv in mine do
    match theirs.find? (fun p => p.1 == kv.1) with
    | none => if bad.isNone then bad := some ("driver: no key " ++ as_key kv.1)
    | some p =>
      if kv.2.nodes.length != p.2.nodes.length then
        if bad.isNone then
          bad := some ("driver key " ++ as_key kv.1 ++ ": nodes "
            ++ toString kv.2.nodes.length ++ " vs " ++ toString p.2.nodes.length)
      else if AbsSat.GraphPath.Model.GPathM.isValid kv.2
          != AbsSat.GraphPath.Model.GPathM.isValid p.2 then
        if bad.isNone then bad := some ("driver key " ++ as_key kv.1 ++ ": validity differs")
  match bad with
  | some m => return { ok := false, msg := m }
  | none => return { ok := true, msg := "" }

def runOneDriver (cnf : String) (path : String) : IO (Bool × Bool × String) := do
  IO.FS.writeFile path cnf
  let gmap ← load_import! path
  match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
  | .error e => return (false, false, s!"parser: {e}")
  | .ok φ =>
    if !AbsSat.Cnf.Dimacs.wfB φ then
      return (true, true, "")
    else
      let r := driverReport φ gmap
      return (false, r.ok, r.msg)

def runDriver (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- pure driver vs the real one: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : DAcc := (0, 0, 0, 0)
  let mut firstFail : Option String := none
  for idx in [0:cases] do
    let (rng1, nv) := rng.below nvSpan
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
    let (skipped, ok, msg) ← runOneDriver cnf "cnfmap_tmp.cnf"
    if skipped then acc := (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2 + 1)
    else if ok then acc := (acc.1 + 1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
    else
      acc := (acc.1 + 1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2)
      if firstFail.isNone then firstFail := some s!"case {idx}: {msg}\n{cnf}"
  IO.println s!"  cases      = {acc.1}"
  IO.println s!"  agreed     = {acc.2.1}"
  IO.println s!"  DISAGREED  = {acc.2.2.1}"
  IO.println s!"  skipped (not well formed) = {acc.2.2.2}"
  match firstFail with
  | some m => IO.println s!"\nfirst disagreement:\n{m}"; return 1
  | none =>
    IO.println "The pure driver runs the same timeline as the real one. ✅"
    return 0

end AbsSat.GraphMap.CnfMapDiff
