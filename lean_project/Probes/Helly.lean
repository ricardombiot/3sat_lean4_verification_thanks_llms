import AbsSat.Cnf.Dimacs
import AbsSat.SatMachine.DiffTest
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.PureDriverImproves
import Std.Data.HashSet
import Std.Data.HashMap

/-! # Helly-3 on the owner tables at the aggressive review's fixpoint (report v116, layer 3)

For every state of the Improves machine (after one aggressive review, `filterAllAgg g []`):

* **pair violations** — `x`, `w` co-owned (each an owner of the other), and a step `j` where their
  owner tables share nothing. `AggConsistent` says there are none.
* **Helly-3 gaps** — `x`, `w`, `v` pairwise co-owned, and a step `j` where the three owner tables
  pairwise share a node but no node is common to all three. A gap is the obstacle to the slice
  argument of v116 (layer 2). Each gap is tagged by whether one of `x`, `w`, `v`, or a node at step
  `j`, has more than one parent (a trace of a join).

Usage: `helly [all] <cnf>...` and `helly random <cases> <minVars> <seed>...`.
-/

namespace Probes.Helly

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)

instance : _root_.Inhabited PathNodeId := ⟨{ id := { step := 0, index := 0 }, parent_id := none }⟩

instance : _root_.Inhabited PNodeM := ⟨{ id := default, title := "", parents := [], sons := [], owners := [] }⟩

def aggLines (φ : Cnf) : List PureLine := Id.run do
  let mut line := pureInit φ
  let mut out := [line]
  for _ in [0:(stepCount φ - 1).toNat] do
    line := line.foldl (fun next kv =>
      (mapSons φ kv.1.step kv.1.index).foldl (fun next d =>
        let h := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid h then insertPure next d h else next) next) []
    out := out ++ [line]
  return out

structure HStat where
  states : Nat := 0
  nodes : Nat := 0
  pairs : Nat := 0
  pairViol : Nat := 0
  triples : Nat := 0
  gaps : Nat := 0
  gapsMulti : Nat := 0
  gapsStepJoin : Nat := 0
  truncated : Nat := 0
  ex : List String := []

def HStat.note (st : HStat) (e : String) : HStat :=
  if st.ex.length < 6 then { st with ex := st.ex ++ [e] } else st

def showPid (p : PathNodeId) : String :=
  s!"{p.id.step}.{p.id.index}" ++ (match p.parent_id with | some q => s!"<{q.step}.{q.index}" | none => "")

/-- Helly-3 census of one state. -/
def census (G : GPathM) (budget : Nat) (st0 : HStat) : HStat := Id.run do
  let mut st := { st0 with states := st0.states + 1, nodes := st0.nodes + G.nodes.length }
  let nodes := G.nodes.toArray
  let ids := nodes.map (·.id)
  let n := nodes.size
  let cs := G.current_step
  -- owner sets, and owners by step
  let sets : Array (Std.HashSet PathNodeId) := nodes.map (fun m => Std.HashSet.ofList m.owners)
  let byStep : Array (Std.HashMap Int (Array PathNodeId)) := nodes.map (fun m =>
    m.owners.foldl (fun (acc : Std.HashMap Int (Array PathNodeId)) q =>
      acc.insert q.id.step ((acc.getD q.id.step #[]).push q)) {})
  let multi : Array Bool := nodes.map (fun m => m.parents.length > 1)
  let stepJoin : Std.HashSet Int := nodes.foldl (fun acc m =>
    if m.parents.length > 1 then acc.insert m.id.id.step else acc) {}
  let co := fun (i j : Nat) => sets[i]!.contains ids[j]! && sets[j]!.contains ids[i]!
  let meets := fun (i j : Nat) (k : Int) =>
    (byStep[i]!.getD k #[]).any (fun r => sets[j]!.contains r)
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  -- co-owned pairs
  let mut pairsOf : Array (Array Nat) := Array.replicate n #[]
  for i in [0:n] do
    for j in [i+1:n] do
      if co i j then
        st := { st with pairs := st.pairs + 1 }
        pairsOf := pairsOf.modify i (·.push j)
        for k in steps do
          if !meets i j k then
            st := ({ st with pairViol := st.pairViol + 1 } : HStat).note
              s!"PAIR {showPid ids[i]!} {showPid ids[j]!} share nothing at step {k}"
  -- triples i < j < l, pairwise co-owned
  let mut left := budget
  for i in [0:n] do
    for j in pairsOf[i]! do
      for l in pairsOf[j]! do
        if left == 0 then continue
        if co i l then
          left := left - 1
          st := { st with triples := st.triples + 1 }
          for k in steps do
            if meets i j k && meets i l k && meets j l k then
              let common := (byStep[i]!.getD k #[]).any (fun r => sets[j]!.contains r && sets[l]!.contains r)
              if !common then
                st := { st with gaps := st.gaps + 1 }
                if multi[i]! || multi[j]! || multi[l]! then st := { st with gapsMulti := st.gapsMulti + 1 }
                if stepJoin.contains k then st := { st with gapsStepJoin := st.gapsStepJoin + 1 }
                st := st.note s!"GAP {showPid ids[i]!} {showPid ids[j]!} {showPid ids[l]!} at step {k} (multi-parent: {multi[i]! || multi[j]! || multi[l]!}, join at step: {stepJoin.contains k})"
  if left == 0 then st := { st with truncated := st.truncated + 1 }
  return st

structure PStat where
  states : Nat := 0
  choiceSteps : Nat := 0
  pins : Nat := 0
  invalid : Nat := 0
  coowners : Nat := 0
  removedCo : Nat := 0
  pinsRemovingCo : Nat := 0
  sliceNodes : Nat := 0
  sliceRemoved : Nat := 0
  outsideKept : Nat := 0
  slicePairs : Nat := 0
  sliceGaps : Nat := 0
  ownerEntries : Nat := 0
  asym : Nat := 0
  ex : List String := []

/-- Every pin at every step with a choice: is the pinned state valid, and does the cascade keep every
node co-owned with the pinned node? -/
def pinCensus (G : GPathM) (st0 : PStat) : PStat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let cs := G.current_step
  -- owner symmetry: q ∈ owners n, q a node m  ⇒  n ∈ owners m
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    G.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  for m in G.nodes do
    for q in m.owners do
      match tbl.get? q with
      | none => pure ()
      | some so =>
        st := { st with ownerEntries := st.ownerEntries + 1 }
        if !so.contains m.id then
          st := { st with asym := st.asym + 1 }
          if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"ASYM {m.id.id.step}.{m.id.id.index} owns-entry {q.id.step}.{q.id.index} (cs {cs})"] }
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let gk := G.gowners.filter (fun q => q.id.step == k)
    let ids := (gk.map (·.id)).eraseDups
    if ids.length > 1 then
      st := { st with choiceSteps := st.choiceSteps + 1 }
      for mid in ids do
        let G' := filterAllAgg G [mid]
        let valid := isValid G'
        st := { st with pins := st.pins + 1 }
        if !valid then
          st := { st with invalid := st.invalid + 1 }
          if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"INVALID pin {mid.step}.{mid.index}"] }
        else
          let alive : Std.HashSet PathNodeId := Std.HashSet.ofList (G'.nodes.map (·.id))
          let mut removed := 0
          for p in gk.filter (fun q => q.id == mid) do
            match G.node? p with
            | none => pure ()
            | some np =>
              for m in G.nodes do
                if m.id != p && np.owners.contains m.id && m.owners.contains p then
                  st := { st with coowners := st.coowners + 1 }
                  if !alive.contains m.id then removed := removed + 1
          if removed > 0 then
            st := { st with removedCo := st.removedCo + removed, pinsRemovingCo := st.pinsRemovingCo + 1 }
          -- the slice by map id: nodes with an owner at step k carrying `mid`
          let inSlice := fun (m : PNodeM) => m.owners.any (fun q => q.id == mid)
          let slice := G.nodes.filter inSlice
          let sliceIds : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
          st := { st with sliceNodes := st.sliceNodes + slice.length }
          for m in G.nodes do
            if sliceIds.contains m.id then
              if !alive.contains m.id then
                st := { st with sliceRemoved := st.sliceRemoved + 1 }
                if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"SLICE NODE REMOVED {m.id.id.step}.{m.id.id.index} by pin {mid.step}.{mid.index}"] }
            else if alive.contains m.id then
              st := { st with outsideKept := st.outsideKept + 1 }
          -- slice gaps: co-owned x, w in the slice with, at some step j, no common owner in the slice
          let arr := slice.toArray
          let sets := arr.map (fun m => Std.HashSet.ofList m.owners)
          for a in [0:arr.size] do
            for b in [a+1:arr.size] do
              if sets[a]!.contains arr[b]!.id && sets[b]!.contains arr[a]!.id then
                st := { st with slicePairs := st.slicePairs + 1 }
                for jj in [0:cs.toNat] do
                  let j : Int := Int.ofNat jj
                  let ok := arr[a]!.owners.any (fun r => r.id.step == j && sets[b]!.contains r && sliceIds.contains r)
                  if !ok then
                    st := { st with sliceGaps := st.sliceGaps + 1 }
                    if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"SLICE GAP {arr[a]!.id.id.step}.{arr[a]!.id.id.index} {arr[b]!.id.id.step}.{arr[b]!.id.id.index} at step {j} (pin {mid.step}.{mid.index})"] }
  return st

def runPins (φ : Cnf) (allLines : Bool) (st0 : PStat) : PStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let mut i := 0
  for line in lines do
    i := i + 1
    if allLines || i == n then
      for kv in line do
        let G := filterAllAgg kv.2 []
        if isValid G then st := pinCensus G st
  return st

def reportP (name : String) (st : PStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} choiceSteps={st.choiceSteps} pins={st.pins} INVALID={st.invalid} | co-owners of pinned nodes={st.coowners} removed by the cascade={st.removedCo} (in {st.pinsRemovingCo} pins) | slice nodes={st.sliceNodes} SLICE_REMOVED={st.sliceRemoved} OUTSIDE_KEPT={st.outsideKept} slicePairs={st.slicePairs} SLICE_GAPS={st.sliceGaps} | ownerEntries={st.ownerEntries} ASYMMETRIC={st.asym} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

def runFormula (φ : Cnf) (allLines : Bool) (st0 : HStat) : HStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let mut i := 0
  for line in lines do
    i := i + 1
    if allLines || i == n then
      for kv in line do
        let G := filterAllAgg kv.2 []
        if isValid G then st := census G 3000000 st
  return st

def report (name : String) (st : HStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} nodes={st.nodes} coOwnedPairs={st.pairs} PAIR_VIOLATIONS={st.pairViol} triples={st.triples} HELLY_GAPS={st.gaps} (multi-parent {st.gapsMulti}, join at step {st.gapsStepJoin}) truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

def loadCnf (path : String) : IO (Option Cnf) := do
  let content ← IO.FS.readFile path
  match AbsSat.Cnf.Dimacs.parse (content.splitOn "\n") with
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

end Probes.Helly

open Probes.Helly in
def main (args : List String) : IO Unit := do
  match args with
  | "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : HStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runFormula φ false st
      let t1 ← IO.monoMsNow
      report s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pins" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPins φ false st
      let t1 ← IO.monoMsNow
      reportP s!"pins seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pins" :: "all" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPins φ true {})
        let t1 ← IO.monoMsNow
        reportP s!"pins {path} [all lines]" st (t1 - t0)
  | "pins" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPins φ false {})
        let t1 ← IO.monoMsNow
        reportP s!"pins {path}" st (t1 - t0)
  | "all" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runFormula φ true {})
        let t1 ← IO.monoMsNow
        report s!"{path} [all lines]" st (t1 - t0)
  | paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runFormula φ false {})
        let t1 ← IO.monoMsNow
        report path st (t1 - t0)
