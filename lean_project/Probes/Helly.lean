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
  keptPairs : Nat := 0
  h3Pred : Nat := 0
  h3Missing : Nat := 0
  h2Pred : Nat := 0
  h2KeptNotPred : Nat := 0
  h2PredNotKept : Nat := 0
  midDropped : Nat := 0
  finalPred : Nat := 0
  finalKeptNotPred : Nat := 0
  finalPredNotKept : Nat := 0
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
          -- which owner entries survive, among surviving nodes
          let after : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
            G'.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
          let before : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
            G.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
          let midOwners := fun (o : Std.HashSet PathNodeId) => o.toList.filter (fun q => q.id == mid)
          for m in G.nodes do
            match after.get? m.id, before.get? m.id with
            | some oa, some ob =>
              for y in m.owners do
                if sliceIds.contains y then
                  st := { st with h3Pred := st.h3Pred + 1 }
                  if !oa.contains y then st := { st with h3Missing := st.h3Missing + 1 }
                  -- H2: y survives iff x and y share an owner carrying mid
                  let pred := match before.get? y with
                    | some oy => (midOwners ob).any (fun q => oy.contains q)
                    | none => false
                  if pred then st := { st with h2Pred := st.h2Pred + 1 }
                  if oa.contains y then st := { st with keptPairs := st.keptPairs + 1 }
                  if oa.contains y && !pred then
                    st := { st with h2KeptNotPred := st.h2KeptNotPred + 1 }
                  if pred && !oa.contains y then
                    st := { st with h2PredNotKept := st.h2PredNotKept + 1 }
                    if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"H2 PRED NOT KEPT {m.id.id.step}.{m.id.id.index} owner {y.id.step}.{y.id.index} pin {mid.step}.{mid.index}"] }
            | _, _ => pure ()
          -- A: entries towards a node carrying mid are never dropped
          -- B: on the final tables, y is an owner of x iff they share an owner carrying mid
          for m in G.nodes do
            match after.get? m.id with
            | none => pure ()
            | some oa =>
              for y in m.owners do
                if y.id == mid && !oa.contains y then
                  st := { st with midDropped := st.midDropped + 1 }
                match after.get? y with
                | none => pure ()
                | some oya =>
                  if y != m.id then
                    let pred := (oa.toList.filter (fun q => q.id == mid)).any (fun q => oya.contains q)
                    if pred then st := { st with finalPred := st.finalPred + 1 }
                    if oa.contains y && !pred then st := { st with finalKeptNotPred := st.finalKeptNotPred + 1 }
                    if pred && !oa.contains y then st := { st with finalPredNotKept := st.finalPredNotKept + 1 }
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
  IO.println s!"{name}: states={st.states} choiceSteps={st.choiceSteps} pins={st.pins} INVALID={st.invalid} | co-owners of pinned nodes={st.coowners} removed by the cascade={st.removedCo} (in {st.pinsRemovingCo} pins) | slice nodes={st.sliceNodes} SLICE_REMOVED={st.sliceRemoved} OUTSIDE_KEPT={st.outsideKept} slicePairs={st.slicePairs} SLICE_GAPS={st.sliceGaps} | ownerEntries={st.ownerEntries} ASYMMETRIC={st.asym} | slice owner entries of survivors={st.h3Pred} dropped={st.h3Missing} kept={st.keptPairs}; H2(share a mid owner) predicted={st.h2Pred} keptNotPredicted={st.h2KeptNotPred} predictedNotKept={st.h2PredNotKept} | A: mid entries dropped={st.midDropped} | B(final tables) predicted={st.finalPred} keptNotPredicted={st.finalKeptNotPred} predictedNotKept={st.finalPredNotKept} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


structure GStat where
  pins : Nat := 0
  rounds : Nat := 0
  maxRounds : Nat := 0
  r0 : Nat := 0
  gfpPairs : Nat := 0
  finalPairs : Nat := 0
  finalNotGfp : Nat := 0
  gfpNotFinal : Nat := 0
  sliceNodes : Nat := 0
  gfpNodesLost : Nat := 0
  ex : List String := []

def GStat.note (st : GStat) (e : String) : GStat :=
  if st.ex.length < 8 then { st with ex := st.ex ++ [e] } else st

/-- The greatest relation inside "both in the slice, an owner entry, a common owner carrying `mid`" that
meets the `AnchoredSurvive.Sup` conditions (par, son, agg), with its coverage; compared with the owner
tables the cascade actually leaves. -/
def gfpCensus (anchor : Bool) (G : GPathM) (st0 : GStat) : GStat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let children : Std.HashMap PathNodeId (Array PathNodeId) := G.nodes.foldl (fun acc m =>
    m.parents.foldl (fun acc c => acc.insert c ((acc.getD c #[]).push m.id)) acc) {}
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let gk := G.gowners.filter (fun q => q.id.step == k)
    let ids := (gk.map (·.id)).eraseDups
    if ids.length > 1 then
      for mid in ids do
        let G' := filterAllAgg G [mid]
        if !isValid G' then continue
        st := { st with pins := st.pins + 1 }
        let slice := G.nodes.filter (fun m => m.owners.any (fun q => q.id == mid))
        let mut S : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
        st := { st with sliceNodes := st.sliceNodes + slice.length }
        let mut R : Std.HashSet (PathNodeId × PathNodeId) := {}
        for m in slice do
          for v in m.owners do
            if S.contains v then
              match tbl.get? v with
              | none => pure ()
              | some nv =>
                if !anchor || m.owners.any (fun q => q.id == mid && nv.owners.contains q) then
                  R := R.insert (m.id, v)
        st := { st with r0 := st.r0 + R.size }
        let mut rounds := 0
        let mut changed := true
        while changed && rounds < 10000 do
          rounds := rounds + 1
          let R0 := R
          let S0 := S
          let rel := fun (a b : PathNodeId) => R0.contains (a, b)
          let inner := fun (p : PathNodeId) => 1 ≤ p.id.step && p.id.step ≤ cs - 2
          let mut R1 : Std.HashSet (PathNodeId × PathNodeId) := {}
          for (x, v) in R0.toList do
            if !(S0.contains x && S0.contains v) then continue
            match tbl.get? x with
            | none => pure ()
            | some nx =>
              let par := x.parent_id.isNone || nx.parents.any (fun c => rel x c && rel c x && rel c v)
              let son := x.id.step == cs - 1 ||
                (children.getD x #[]).any (fun c => rel x c && rel c x && rel c v)
              let agg := !(inner x && inner v) ||
                steps.all (fun l => nx.owners.any (fun z => z.id.step == l && rel x z && rel v z))
              if par && son && agg then R1 := R1.insert (x, v)
          let mut S1 : Std.HashSet PathNodeId := {}
          for x in S0.toList do
            match tbl.get? x with
            | none => pure ()
            | some nx =>
              if steps.all (fun l => nx.owners.any (fun v => v.id.step == l && R1.contains (x, v))) then
                S1 := S1.insert x
          changed := R1.size != R0.size || S1.size != S0.size
          R := R1
          S := S1
        st := { st with rounds := st.rounds + rounds, maxRounds := max st.maxRounds rounds }
        let Rl := R.toList.filter (fun (x, v) => S.contains x && S.contains v)
        let Rs : Std.HashSet (PathNodeId × PathNodeId) := Std.HashSet.ofList Rl
        st := { st with gfpPairs := st.gfpPairs + Rl.length }
        for m in slice do
          if !S.contains m.id then
            st := ({ st with gfpNodesLost := st.gfpNodesLost + 1 } : GStat).note
              s!"GFP LOSES {showPid m.id} (pin {mid.step}.{mid.index}, cs {cs})"
        let alive : Std.HashSet PathNodeId := Std.HashSet.ofList (G'.nodes.map (·.id))
        let mut fin : Std.HashSet (PathNodeId × PathNodeId) := {}
        for m in G'.nodes do
          for v in m.owners do
            if alive.contains v then fin := fin.insert (m.id, v)
        st := { st with finalPairs := st.finalPairs + fin.size }
        for (x, v) in fin.toList do
          if !Rs.contains (x, v) then
            st := ({ st with finalNotGfp := st.finalNotGfp + 1 } : GStat).note
              s!"FINAL NOT GFP {showPid x} owns {showPid v} (pin {mid.step}.{mid.index}, cs {cs})"
        for (x, v) in Rl do
          if !fin.contains (x, v) then st := { st with gfpNotFinal := st.gfpNotFinal + 1 }
  return st

def runGfp (anchor : Bool) (φ : Cnf) (allLines : Bool) (st0 : GStat) : GStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let mut i := 0
  for line in lines do
    i := i + 1
    if allLines || i == n then
      for kv in line do
        let G := filterAllAgg kv.2 []
        if isValid G then st := gfpCensus anchor G st
  return st

def reportG (name : String) (st : GStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} sliceNodes={st.sliceNodes} GFP_NODES_LOST={st.gfpNodesLost} | R0={st.r0} gfp={st.gfpPairs} final={st.finalPairs} FINAL_NOT_GFP={st.finalNotGfp} gfpNotFinal={st.gfpNotFinal} | rounds={st.rounds} maxRounds={st.maxRounds} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

structure RStat where
  pins : Nat := 0
  maxRounds : Nat := 0
  killed : Array Nat := Array.replicate 16 0
  fAgg : Array Nat := Array.replicate 16 0
  fPar : Array Nat := Array.replicate 16 0
  fSon : Array Nat := Array.replicate 16 0
  onlyAgg : Array Nat := Array.replicate 16 0
  onlyPar : Array Nat := Array.replicate 16 0
  onlySon : Array Nat := Array.replicate 16 0
  aggAtMid : Array Nat := Array.replicate 16 0
  noCarrier : Array Nat := Array.replicate 16 0
  boundary : Array Nat := Array.replicate 16 0
  interiorKilled : Array Nat := Array.replicate 16 0
  interiorNonAgg : Array Nat := Array.replicate 16 0
  nodesLost : Array Nat := Array.replicate 16 0
  cellsDrop : Array Nat := Array.replicate 16 0
  cellsOne : Array Nat := Array.replicate 16 0
  cellsOneStart : Nat := 0
  cellsOneEnd : Nat := 0
  cellsOneEndCarrierOnly : Nat := 0
  cells : Nat := 0
  minSupportEnd : Nat := 1000000
  ex : List String := []

def bump (a : Array Nat) (r : Nat) (k : Nat := 1) : Array Nat :=
  let i := min r 15
  a.modify i (· + k)

/-- The rounds of the largest `Sup` relation on the slice: what falls in each round, and why. -/
def roundsCensus (G : GPathM) (st0 : RStat) : RStat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let children : Std.HashMap PathNodeId (Array PathNodeId) := G.nodes.foldl (fun acc m =>
    m.parents.foldl (fun acc c => acc.insert c ((acc.getD c #[]).push m.id)) acc) {}
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let gk := G.gowners.filter (fun q => q.id.step == k)
    let ids := (gk.map (·.id)).eraseDups
    if ids.length > 1 then
      for mid in ids do
        if !isValid (filterAllAgg G [mid]) then continue
        st := { st with pins := st.pins + 1 }
        let slice := G.nodes.filter (fun m => m.owners.any (fun q => q.id == mid))
        let mut S : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
        let S00 := S
        let mut R : Std.HashSet (PathNodeId × PathNodeId) := {}
        for m in slice do
          for v in m.owners do
            if S00.contains v then R := R.insert (m.id, v)
        -- a cell (x, l) is nontrivial when l is neither x's own step nor the pinned step
        let nontrivial := fun (x : PathNodeId) (l : Int) => l != x.id.step && l != mid.step
        let support := fun (Rc : Std.HashSet (PathNodeId × PathNodeId)) (x : PathNodeId) (l : Int) =>
          match tbl.get? x with
          | none => 0
          | some nx => (nx.owners.filter (fun v => v.id.step == l && Rc.contains (x, v))).length
        let mut prevSup : Std.HashMap (PathNodeId × Int) Nat := {}
        for x in S00.toList do
          for l in steps do
            if nontrivial x l then
              let c := support R x l
              prevSup := prevSup.insert (x, l) c
              if c == 1 then st := { st with cellsOneStart := st.cellsOneStart + 1 }
        st := { st with cells := st.cells + prevSup.size }
        let carrierShared := fun (x v : PathNodeId) =>
          match tbl.get? x, tbl.get? v with
          | some nx, some nv => nx.owners.any (fun q => q.id == mid && nv.owners.contains q)
          | _, _ => false
        let mut round := 0
        let mut changed := true
        while changed && round < 1000 do
          let R0 := R
          let S0 := S
          let rel := fun (a b : PathNodeId) => R0.contains (a, b)
          let inner := fun (p : PathNodeId) => 1 ≤ p.id.step && p.id.step ≤ cs - 2
          let mut R1 : Std.HashSet (PathNodeId × PathNodeId) := {}
          for (x, v) in R0.toList do
            match tbl.get? x with
            | none => pure ()
            | some nx =>
              if !(S0.contains x && S0.contains v) then
                continue
              let par := x.parent_id.isNone || nx.parents.any (fun c => rel x c && rel c x && rel c v)
              let son := x.id.step == cs - 1 ||
                (children.getD x #[]).any (fun c => rel x c && rel c x && rel c v)
              let failSteps := steps.filter (fun l => !nx.owners.any (fun z => z.id.step == l && rel x z && rel v z))
              let agg := failSteps.isEmpty && rel v x
              if par && son && agg then
                R1 := R1.insert (x, v)
              else
                st := { st with killed := bump st.killed round }
                if !agg then st := { st with fAgg := bump st.fAgg round }
                if !par then st := { st with fPar := bump st.fPar round }
                if !son then st := { st with fSon := bump st.fSon round }
                if !agg && par && son then st := { st with onlyAgg := bump st.onlyAgg round }
                if agg && !par && son then st := { st with onlyPar := bump st.onlyPar round }
                if agg && par && !son then st := { st with onlySon := bump st.onlySon round }
                if failSteps.contains mid.step then st := { st with aggAtMid := bump st.aggAtMid round }
                if !carrierShared x v then st := { st with noCarrier := bump st.noCarrier round }
                if !(inner x && inner v) then st := { st with boundary := bump st.boundary round }
                else
                  st := { st with interiorKilled := bump st.interiorKilled round }
                  if agg then
                    st := { st with interiorNonAgg := bump st.interiorNonAgg round }
                    if st.ex.length < 10 then
                      st := { st with ex := st.ex ++ [s!"INTERIOR NON-AGG R{round} pin {mid.step}.{mid.index}: {showPid x} -/-> {showPid v} par {par} son {son}"] }
                if round ≥ 1 && st.ex.length < 10 then
                  st := { st with ex := st.ex ++ [s!"R{round} pin {mid.step}.{mid.index}: {showPid x} -/-> {showPid v} agg-fail-steps {failSteps.take 4} par {par} son {son} carrier {carrierShared x v}"] }
          let mut S1 : Std.HashSet PathNodeId := {}
          for x in S0.toList do
            match tbl.get? x with
            | none => pure ()
            | some nx =>
              if steps.all (fun l => nx.owners.any (fun v => v.id.step == l && R1.contains (x, v))) then
                S1 := S1.insert x
              else
                st := { st with nodesLost := bump st.nodesLost round }
          -- supports after the round
          for x in S1.toList do
            for l in steps do
              if nontrivial x l then
                let c := support R1 x l
                if c < prevSup.getD (x, l) 0 then st := { st with cellsDrop := bump st.cellsDrop round }
                if c == 1 then st := { st with cellsOne := bump st.cellsOne round }
                prevSup := prevSup.insert (x, l) c
          changed := R1.size != R0.size || S1.size != S0.size
          R := R1
          S := S1
          round := round + 1
        st := { st with maxRounds := max st.maxRounds round }
        for x in S.toList do
          for l in steps do
            if nontrivial x l then
              let c := support R x l
              st := { st with minSupportEnd := min st.minSupportEnd c }
              if c == 1 then
                st := { st with cellsOneEnd := st.cellsOneEnd + 1 }
  return st

def runRounds (φ : Cnf) (st0 : RStat) : RStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  match lines.getLast? with
  | none => pure ()
  | some line =>
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := roundsCensus G st
  return st

def reportR (name : String) (st : RStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} maxRounds={st.maxRounds} nontrivial cells={st.cells} single-support cells start={st.cellsOneStart} end={st.cellsOneEnd} minSupportEnd={st.minSupportEnd} | {ms}ms"
  let n := min st.maxRounds 16
  for r in [0:n] do
    IO.println s!"  round {r}: killed={st.killed[r]!} failAgg={st.fAgg[r]!} failPar={st.fPar[r]!} failSon={st.fSon[r]!} onlyAgg={st.onlyAgg[r]!} onlyPar={st.onlyPar[r]!} onlySon={st.onlySon[r]!} aggFailsAtPinnedStep={st.aggAtMid[r]!} noCarrier={st.noCarrier[r]!} boundaryPair={st.boundary[r]!} interiorKilled={st.interiorKilled[r]!} INTERIOR_NON_AGG={st.interiorNonAgg[r]!} NODES_LOST={st.nodesLost[r]!} cellsDropped={st.cellsDrop[r]!} singleSupportCells={st.cellsOne[r]!}"
  for e in st.ex do IO.println s!"  EX {e}"

structure HerStat where
  pins : Nat := 0
  r1Pairs : Nat := 0
  witnesses : Nat := 0
  badWitnesses : Nat := 0
  badBoundaryZ : Nat := 0
  cellsNoGood : Nat := 0
  ex : List String := []

/-- Slice pair consistency `SPC x v`: both in the slice, `v` owns-entry of `x`, and at every step a
common owner in the slice. Is every witness of an interior `SPC` pair itself `SPC` with both ends? -/
def heredCensus (G : GPathM) (st0 : HerStat) : HerStat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  let _inner := fun (p : PathNodeId) => 1 ≤ p.id.step && p.id.step ≤ cs - 2
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let gk := G.gowners.filter (fun q => q.id.step == k)
    let ids := (gk.map (·.id)).eraseDups
    if ids.length > 1 then
      for mid in ids do
        if !isValid (filterAllAgg G [mid]) then continue
        st := { st with pins := st.pins + 1 }
        let slice := G.nodes.filter (fun m => m.owners.any (fun q => q.id == mid))
        let S : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
        let E := fun (x v : PathNodeId) => S.contains x && S.contains v &&
          (match tbl.get? x with | some nx => nx.owners.contains v | none => false)
        let wit : PathNodeId → PathNodeId → Int → List PathNodeId := fun x v l =>
          match tbl.get? x with
          | some nx => nx.owners.filter (fun (z : PathNodeId) => z.id.step == l && E x z && E v z)
          | none => []
        let mut SPC : Std.HashSet (PathNodeId × PathNodeId) := {}
        for m in slice do
          for v in m.owners do
            if E m.id v && steps.all (fun l => !(wit m.id v l).isEmpty) then
              SPC := SPC.insert (m.id, v)
        for (x, v) in SPC.toList do
          if true then
            st := { st with r1Pairs := st.r1Pairs + 1 }
            for l in steps do
              let ws := wit x v l
              let mut good := false
              for z in ws do
                st := { st with witnesses := st.witnesses + 1 }
                if SPC.contains (x, z) && SPC.contains (v, z) then good := true
                else
                  st := { st with badWitnesses := st.badWitnesses + 1 }
                  if st.ex.length < 6 then
                    st := { st with ex := st.ex ++ [s!"BAD WITNESS pin {mid.step}.{mid.index}: {showPid x} {showPid v} via {showPid z} at {l}"] }
              if !good then st := { st with cellsNoGood := st.cellsNoGood + 1 }
  return st

def runHered (φ : Cnf) (st0 : HerStat) : HerStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  match lines.getLast? with
  | none => pure ()
  | some line =>
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := heredCensus G st
  return st

structure SpcStat where
  pins : Nat := 0
  carriers : Array Nat := Array.replicate 6 0
  spcInterior : Nat := 0
  triangles : Nat := 0
  triangleFail : Nat := 0
  cells : Nat := 0
  cellsNoHalf : Nat := 0
  witnesses : Nat := 0
  witXonly : Nat := 0
  witVonly : Nat := 0
  witBoth : Nat := 0
  witNone : Nat := 0
  ePairsInterior : Nat := 0
  nonSpcInterior : Nat := 0
  failOnlyAtPinned : Nat := 0
  boundaryPins : Nat := 0
  badAtPinned : Nat := 0
  badBetween : Nat := 0
  badOutside : Nat := 0
  badAtBoundaryStep : Nat := 0
  badPinBoundary : Nat := 0
  badDist : Array Nat := Array.replicate 8 0
  ex : List String := []

/-- Structure of `SPC` (slice pair consistency) on the interior steps. -/
def spcCensus (G : GPathM) (st0 : SpcStat) : SpcStat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  let inner := fun (p : PathNodeId) => 1 ≤ p.id.step && p.id.step ≤ cs - 2
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let gk := G.gowners.filter (fun q => q.id.step == k)
    let ids := (gk.map (·.id)).eraseDups
    if ids.length > 1 then
      for mid in ids do
        if !isValid (filterAllAgg G [mid]) then continue
        st := { st with pins := st.pins + 1 }
        if mid.step == 0 || mid.step == cs - 1 then st := { st with boundaryPins := st.boundaryPins + 1 }
        let nc := (G.nodes.filter (fun m => m.id.id == mid)).length
        st := { st with carriers := st.carriers.modify (min nc 5) (· + 1) }
        let slice := G.nodes.filter (fun m => m.owners.any (fun q => q.id == mid))
        let S : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
        let E := fun (x v : PathNodeId) => S.contains x && S.contains v &&
          (match tbl.get? x with | some nx => nx.owners.contains v | none => false)
        let wit : PathNodeId → PathNodeId → Int → List PathNodeId := fun x v l =>
          match tbl.get? x with
          | some nx => nx.owners.filter (fun (z : PathNodeId) => z.id.step == l && E x z && E v z)
          | none => []
        let mut SPC : Std.HashSet (PathNodeId × PathNodeId) := {}
        for m in slice do
          for v in m.owners do
            if E m.id v then
              let fails := steps.filter (fun l => (wit m.id v l).isEmpty)
              if fails.isEmpty then SPC := SPC.insert (m.id, v)
              else if inner m.id && inner v then
                st := { st with nonSpcInterior := st.nonSpcInterior + 1 }
                if fails == [mid.step] then st := { st with failOnlyAtPinned := st.failOnlyAtPinned + 1 }
              if inner m.id && inner v then st := { st with ePairsInterior := st.ePairsInterior + 1 }
        -- SPC neighbours of each node
        let nbr : Std.HashMap PathNodeId (Array PathNodeId) := SPC.toList.foldl (fun acc (x, v) =>
          acc.insert x ((acc.getD x #[]).push v)) {}
        for (x, v) in SPC.toList do
          if !(inner x && inner v) || x == v then continue
          st := { st with spcInterior := st.spcInterior + 1 }
          -- 1. triangle closure: SPC x v, SPC x z, z owns-entry of v  ⇒  SPC v z
          for z in nbr.getD x #[] do
            if inner z && z != v && z != x && E v z then
              st := { st with triangles := st.triangles + 1 }
              if !SPC.contains (v, z) then
                st := { st with triangleFail := st.triangleFail + 1 }
                if st.ex.length < 6 then
                  st := { st with ex := st.ex ++ [s!"TRIANGLE pin {mid.step}.{mid.index}: SPC {showPid x}-{showPid v}, SPC {showPid x}-{showPid z}, not SPC {showPid v}-{showPid z}"] }
          -- 2. witnesses by which end they are SPC with
          for l in steps do
            if l == x.id.step || l == v.id.step || l == mid.step then continue
            let ws := (wit x v l).filter inner
            if ws.isEmpty then continue
            st := { st with cells := st.cells + 1 }
            let mut half := false
            for z in ws do
              st := { st with witnesses := st.witnesses + 1 }
              let a := SPC.contains (x, z)
              let b := SPC.contains (v, z)
              if a then half := true
              if a && b then st := { st with witBoth := st.witBoth + 1 }
              else if a then
                st := { st with witXonly := st.witXonly + 1 }
                if mid.step == 0 || mid.step == cs - 1 then st := { st with badPinBoundary := st.badPinBoundary + 1 }
                -- where does SPC v z fail?
                for l' in steps do
                  if (wit v z l').isEmpty then
                    let lo := min v.id.step z.id.step
                    let hi := max v.id.step z.id.step
                    if l' == mid.step then st := { st with badAtPinned := st.badAtPinned + 1 }
                    else if lo < l' && l' < hi then st := { st with badBetween := st.badBetween + 1 }
                    else st := { st with badOutside := st.badOutside + 1 }
                    if l' == 0 || l' == cs - 1 then st := { st with badAtBoundaryStep := st.badAtBoundaryStep + 1 }
                    let d := if l' < lo then lo - l' else if l' > hi then l' - hi else 0
                    st := { st with badDist := st.badDist.modify (min d.toNat 7) (· + 1) }
              else if b then st := { st with witVonly := st.witVonly + 1 }
              else st := { st with witNone := st.witNone + 1 }
            if !half then st := { st with cellsNoHalf := st.cellsNoHalf + 1 }
  return st

def runSpc (φ : Cnf) (st0 : SpcStat) : SpcStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  match lines.getLast? with
  | none => pure ()
  | some line =>
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := spcCensus G st
  return st

structure P2Stat where
  pairs : Nat := 0
  valid : Nat := 0
  invalid : Nat := 0
  sliceRemoved : Nat := 0
  outsideKept : Nat := 0
  seqDiffers : Nat := 0
  invalidWithFullSlice : Nat := 0
  invalidSliceEmptyStep : Nat := 0
  ex : List String := []

/-- Every pair of pins at different steps: exact double slice, and order independence. -/
def pins2Census (G : GPathM) (st0 : P2Stat) : P2Stat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let mut choice : List NodeId := []
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let ids := ((G.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
    if ids.length > 1 then choice := choice ++ ids
  let ids := G.nodes.map (·.id)
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  for a in choice do
    let Ga := filterAllAgg G [a]
    for b in choice do
      if b.step ≤ a.step then continue
      st := { st with pairs := st.pairs + 1 }
      let G2 := filterAllAgg G [a, b]
      let slice := G.nodes.filter (fun m => m.owners.any (fun q => q.id == a) && m.owners.any (fun q => q.id == b))
      let sliceIds : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
      if isValid G2 then
        st := { st with valid := st.valid + 1 }
        let alive : Std.HashSet PathNodeId := Std.HashSet.ofList (G2.nodes.map (·.id))
        for x in ids do
          if sliceIds.contains x && !alive.contains x then
            st := { st with sliceRemoved := st.sliceRemoved + 1 }
            if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"2-PIN SLICE NODE REMOVED {showPid x} pins {a.step}.{a.index} {b.step}.{b.index}"] }
          if !sliceIds.contains x && alive.contains x then st := { st with outsideKept := st.outsideKept + 1 }
        -- order: pin a, review, pin b, review
        let Gs := if isValid Ga then filterAllAgg Ga [b] else Ga
        let aliveS : List PathNodeId := Gs.nodes.map (·.id)
        if aliveS.length != G2.nodes.length || aliveS.any (fun x => !alive.contains x) then
          st := { st with seqDiffers := st.seqDiffers + 1 }
      else
        st := { st with invalid := st.invalid + 1 }
        let full := steps.all (fun l => slice.any (fun m => m.id.id.step == l))
        if full then
          st := { st with invalidWithFullSlice := st.invalidWithFullSlice + 1 }
        else st := { st with invalidSliceEmptyStep := st.invalidSliceEmptyStep + 1 }
  return st

def runPins2 (φ : Cnf) (st0 : P2Stat) : P2Stat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  match lines.getLast? with
  | none => pure ()
  | some line =>
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := pins2Census G st
  return st

structure D2Stat where
  firstPins : Nat := 0
  secondPins : Nat := 0
  invalid : Nat := 0
  sliceNodes : Nat := 0
  sliceRemoved : Nat := 0
  outsideKept : Nat := 0
  lostCarrier : Nat := 0
  removedBoundaryPin : Nat := 0
  removedInteriorPin : Nat := 0
  interiorSecondPins : Nat := 0
  pinsRemoving : Nat := 0
  removedSteps : List Int := []
  ex : List String := []

/-- Depth two of the reader: after a valid pin `a`, every pin `b` of the new state, with the slice
of `b` read in the new state. Also: nodes of the base double slice that lost their `b` carrier. -/
def depth2Census (G : GPathM) (st0 : D2Stat) : D2Stat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let choiceOf := fun (H : GPathM) => Id.run do
    let mut out : List NodeId := []
    for i in [0:cs.toNat] do
      let k : Int := Int.ofNat i
      let ids := ((H.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
      if ids.length > 1 then out := out ++ ids
    return out
  for a in choiceOf G do
    let Ga := filterAllAgg G [a]
    if !isValid Ga then continue
    st := { st with firstPins := st.firstPins + 1 }
    for b in choiceOf Ga do
      st := { st with secondPins := st.secondPins + 1 }
      let bBoundary := b.step == 0 || b.step == cs - 1
      if !bBoundary then st := { st with interiorSecondPins := st.interiorSecondPins + 1 }
      let Gb := filterAllAgg Ga [b]
      if !isValid Gb then
        st := { st with invalid := st.invalid + 1 }
        if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"INVALID depth-2 pin {a.step}.{a.index} then {b.step}.{b.index}"] }
        continue
      let slice := Ga.nodes.filter (fun m => m.owners.any (fun q => q.id == b))
      let sliceIds : Std.HashSet PathNodeId := Std.HashSet.ofList (slice.map (·.id))
      st := { st with sliceNodes := st.sliceNodes + slice.length }
      let alive : Std.HashSet PathNodeId := Std.HashSet.ofList (Gb.nodes.map (·.id))
      let before := st.sliceRemoved
      for m in Ga.nodes do
        if sliceIds.contains m.id && !alive.contains m.id then
          st := { st with sliceRemoved := st.sliceRemoved + 1 }
          if bBoundary then st := { st with removedBoundaryPin := st.removedBoundaryPin + 1 }
          else st := { st with removedInteriorPin := st.removedInteriorPin + 1 }
          if !st.removedSteps.contains m.id.id.step then st := { st with removedSteps := st.removedSteps ++ [m.id.id.step] }
          if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"DEPTH-2 SLICE NODE REMOVED {showPid m.id} pins {a.step}.{a.index} then {b.step}.{b.index}"] }
        if !sliceIds.contains m.id && alive.contains m.id then st := { st with outsideKept := st.outsideKept + 1 }
      if st.sliceRemoved > before then st := { st with pinsRemoving := st.pinsRemoving + 1 }
      -- base double slice members alive in Ga that lost every b carrier
      for m in G.nodes do
        if m.owners.any (fun q => q.id == a) && m.owners.any (fun q => q.id == b) then
          match Ga.node? m.id with
          | some m' => if !(m'.owners.any (fun q => q.id == b)) then st := { st with lostCarrier := st.lostCarrier + 1 }
          | none => pure ()
  return st

def runDepth2 (φ : Cnf) (st0 : D2Stat) : D2Stat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  match lines.getLast? with
  | none => pure ()
  | some line =>
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := depth2Census G st
  return st

structure WStat where
  walks : Nat := 0
  states : Nat := 0
  choiceStates : Nat := 0
  pins : Nat := 0
  invalidPins : Nat := 0
  inexactPins : Nat := 0
  inexactBoundaryPins : Nat := 0
  inexactInteriorPins : Nat := 0
  statesNoExact : Nat := 0
  statesInteriorChoice : Nat := 0
  statesInteriorChoiceNoExactInterior : Nat := 0
  statesOnlyBoundaryChoice : Nat := 0
  statesOnlyBoundaryNoExact : Nat := 0
  statesNoValidPin : Nat := 0
  ex : List String := []

/-- Is the pin of `mid` on `H` valid, and does it keep its slice exactly? -/
def pinCheck (H : GPathM) (mid : NodeId) : Bool × Bool := Id.run do
  let H' := filterAllAgg H [mid]
  if !isValid H' then return (false, false)
  let alive : Std.HashSet PathNodeId := Std.HashSet.ofList (H'.nodes.map (·.id))
  let exact := H.nodes.all (fun m => (m.owners.any (fun q => q.id == mid)) == alive.contains m.id)
  return (true, exact)

/-- Random reader walks: at every visited state, every pin at every step with a choice. -/
def walkCensus (G : GPathM) (walks : Nat) (seed : Nat) (st0 : WStat) : WStat := Id.run do
  let mut st := st0
  let cs := G.current_step
  let mut rng := seed
  let mid0 : NodeId := { step := 0, index := 0 }
  for _ in [0:walks] do
    st := { st with walks := st.walks + 1 }
    let mut H := G
    let mut go := true
    let mut depth := 0
    while go && depth < 200 do
      depth := depth + 1
      st := { st with states := st.states + 1 }
      let mut cands : List NodeId := []
      for i in [0:cs.toNat] do
        let k : Int := Int.ofNat i
        let ids := ((H.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
        if ids.length > 1 then cands := cands ++ ids
      if cands.isEmpty then
        go := false
        continue
      st := { st with choiceStates := st.choiceStates + 1 }
      let isB := fun (m : NodeId) => m.step == 0 || m.step == cs - 1
      let hasInterior := cands.any (fun m => !isB m)
      if hasInterior then st := { st with statesInteriorChoice := st.statesInteriorChoice + 1 }
      else st := { st with statesOnlyBoundaryChoice := st.statesOnlyBoundaryChoice + 1 }
      let mut valid : List NodeId := []
      let mut anyExact := false
      let mut anyExactInterior := false
      for m in cands do
        st := { st with pins := st.pins + 1 }
        let (v, e) := pinCheck H m
        if !v then st := { st with invalidPins := st.invalidPins + 1 }
        else
          valid := valid ++ [m]
          if e then
            anyExact := true
            if !isB m then anyExactInterior := true
          else
            st := { st with inexactPins := st.inexactPins + 1 }
            if isB m then st := { st with inexactBoundaryPins := st.inexactBoundaryPins + 1 }
            else
              st := { st with inexactInteriorPins := st.inexactInteriorPins + 1 }
              if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"INEXACT INTERIOR pin {m.step}.{m.index} at depth {depth}"] }
      if !anyExact then
        st := { st with statesNoExact := st.statesNoExact + 1 }
        if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"STATE WITHOUT EXACT PIN at depth {depth} ({cands.length} candidates, {valid.length} valid)"] }
      if hasInterior && !anyExactInterior then st := { st with statesInteriorChoiceNoExactInterior := st.statesInteriorChoiceNoExactInterior + 1 }
      if !hasInterior && !anyExact then st := { st with statesOnlyBoundaryNoExact := st.statesOnlyBoundaryNoExact + 1 }
      if valid.isEmpty then
        st := { st with statesNoValidPin := st.statesNoValidPin + 1 }
        go := false
        continue
      rng := (rng * 1103515245 + 12345) % 2147483648
      let pick := valid.getD (rng % valid.length) mid0
      H := filterAllAgg H [pick]
  return st

def runWalk (φ : Cnf) (walks seed : Nat) (st0 : WStat) : WStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  match lines.getLast? with
  | none => pure ()
  | some line =>
    let mut sd := seed
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then
        st := walkCensus G walks sd st
        sd := sd + 7919
  return st

def runWalkAll (φ : Cnf) (walks seed : Nat) (st0 : WStat) : WStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  let mut sd := seed
  for line in lines do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then
        st := walkCensus G walks sd st
        sd := sd + 7919
  return st

def reportW (name : String) (st : WStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: walks={st.walks} states={st.states} withChoice={st.choiceStates} pins={st.pins} INVALID={st.invalidPins} inexact={st.inexactPins} (boundary {st.inexactBoundaryPins}, INTERIOR {st.inexactInteriorPins}) | states: interior choice={st.statesInteriorChoice} (NO_EXACT_INTERIOR {st.statesInteriorChoiceNoExactInterior}) only-boundary choice={st.statesOnlyBoundaryChoice} (NO_EXACT {st.statesOnlyBoundaryNoExact}) STATES_NO_EXACT={st.statesNoExact} STATES_NO_VALID={st.statesNoValidPin} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

/-- Is there a full chain (one node per step, pairwise mutual owners) through the chosen nodes?
Branches on the remaining step with fewest candidates; the state counts search nodes left. -/
partial def goClique (own : Std.HashMap PathNodeId (Std.HashSet PathNodeId))
    (byStep : Std.HashMap Int (Array PathNodeId)) (chosen : List PathNodeId) (rem : List Int) :
    StateM Nat Bool := do
  match rem with
  | [] => return true
  | _ =>
    let budget ← get
    if budget == 0 then return false
    set (budget - 1)
    let cands := rem.map (fun l => (l, (byStep.getD l #[]).filter (fun c =>
      chosen.all (fun y => (own.getD y {}).contains c && (own.getD c {}).contains y))))
    if cands.any (fun p => p.2.isEmpty) then return false
    match cands with
    | [] => return true
    | first :: rest =>
      let best := rest.foldl (fun acc p => if p.2.size < acc.2.size then p else acc) first
      let rem' := rem.filter (· != best.1)
      for c in best.2 do
        if ← goClique own byStep (c :: chosen) rem' then return true
      return false

structure CStat where
  states : Nat := 0
  nodes : Nat := 0
  nodesNoChain : Nat := 0
  pairs : Nat := 0
  pairsNoChain : Nat := 0
  truncated : Nat := 0
  statesNoChainAtAll : Nat := 0
  ex : List String := []

def chainCensus (G : GPathM) (tag : String) (st0 : CStat) : CStat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let cs := G.current_step
  let own : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    G.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let byStep : Std.HashMap Int (Array PathNodeId) :=
    G.nodes.foldl (fun acc m => acc.insert m.id.id.step ((acc.getD m.id.id.step #[]).push m.id)) {}
  let steps : List Int := (List.range cs.toNat).map (fun (s : Nat) => Int.ofNat s)
  let budget := 200000
  let mut anyChain := false
  for m in G.nodes do
    let x := m.id
    st := { st with nodes := st.nodes + 1 }
    let (ok, left) := (goClique own byStep [x] (steps.filter (· != x.id.step))).run budget
    if left == 0 && !ok then st := { st with truncated := st.truncated + 1 }
    if ok then anyChain := true
    else
      st := { st with nodesNoChain := st.nodesNoChain + 1 }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"NODE WITHOUT CHAIN {showPid x} ({tag}, cs {cs})"] }
    for w in m.owners do
      if w.id.step ≤ x.id.step then continue
      if !((own.getD w {}).contains x) then continue
      st := { st with pairs := st.pairs + 1 }
      let (ok2, left2) := (goClique own byStep [x, w] (steps.filter (fun l => l != x.id.step && l != w.id.step))).run budget
      if left2 == 0 && !ok2 then st := { st with truncated := st.truncated + 1 }
      if !ok2 then
        st := { st with pairsNoChain := st.pairsNoChain + 1 }
        if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"PAIR WITHOUT CHAIN {showPid x} {showPid w} ({tag}, cs {cs})"] }
  if !anyChain && !G.nodes.isEmpty then st := { st with statesNoChainAtAll := st.statesNoChainAtAll + 1 }
  return st

/-- Base states of every line (or the last), and optionally reader walks from them. -/
def runChains (φ : Cnf) (allLines : Bool) (walks depth seed : Nat) (st0 : CStat) : CStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let mut rng := seed
  let mut i := 0
  for line in lines do
    i := i + 1
    if !(allLines || i == n) then continue
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      st := chainCensus G s!"line {i - 1} base" st
      for _ in [0:walks] do
        let mut H := G
        for d in [0:depth] do
          let cs := H.current_step
          let mut cands : List NodeId := []
          for j in [0:cs.toNat] do
            let k : Int := Int.ofNat j
            let ids := ((H.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
            if ids.length > 1 then cands := cands ++ ids
          if cands.isEmpty then break
          rng := (rng * 1103515245 + 12345) % 2147483648
          let pick := cands.getD (rng % cands.length) { step := 0, index := 0 }
          let H' := filterAllAgg H [pick]
          if !isValid H' then break
          H := H'
          st := chainCensus H s!"line {i - 1} reader depth {d + 1}" st
  return st

def reportC (name : String) (st : CStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} nodes={st.nodes} NODES_WITHOUT_CHAIN={st.nodesNoChain} ownerPairs={st.pairs} PAIRS_WITHOUT_CHAIN={st.pairsNoChain} statesWithNoChainAtAll={st.statesNoChainAtAll} truncatedSearches={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

/-- One advance of the Improves driver (the same step `aggLines` iterates). -/
def advanceLine (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv =>
    (mapSons φ kv.1.step kv.1.index).foldl (fun next d =>
      let h := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
      if isValid h then insertPure next d h else next) next) []

structure KStat where
  pins : Nat := 0
  bothValid : Nat := 0
  bothInvalid : Nat := 0
  pinValidRunNot : Nat := 0
  runValidPinNot : Nat := 0
  nodesEqual : Nat := 0
  pinExtraNodes : Nat := 0
  runExtraNodes : Nat := 0
  ownersEqual : Nat := 0
  pinExtraOwners : Nat := 0
  runExtraOwners : Nat := 0
  ex : List String := []

/-- Pinning `q` in a final state versus running the machine on the branch of `q` alone. -/
def runCommute (φ : Cnf) (st0 : KStat) : KStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let lineArr := lines.toArray
  match lines.getLast? with
  | none => return st
  | some final =>
    -- restricted runs, cached by pin
    let mut cache : Std.HashMap NodeId PureLine := {}
    for kv in final do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      let cs := G.current_step
      for i in [0:cs.toNat] do
        let k : Int := Int.ofNat i
        let ids := ((G.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
        if ids.length ≤ 1 then continue
        for q in ids do
          st := { st with pins := st.pins + 1 }
          let restricted ← match cache.get? q with
            | some r => pure r
            | none =>
              let start := (lineArr[q.step.toNat]!).filter (fun e => e.1 == q)
              let mut line := start
              for _ in [0:(n - 1 - q.step.toNat)] do
                line := advanceLine φ line
              pure line
          cache := cache.insert q restricted
          let Fq := filterAllAgg G [q]
          let runState := (restricted.find? (fun e => e.1 == kv.1)).map (fun e => filterAllAgg e.2 [])
          let pv := isValid Fq
          let rv := match runState with | some r => isValid r | none => false
          if pv && rv then st := { st with bothValid := st.bothValid + 1 }
          else if !pv && !rv then st := { st with bothInvalid := st.bothInvalid + 1 }
          else if pv then
            st := { st with pinValidRunNot := st.pinValidRunNot + 1 }
            if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"PIN VALID, RUN NOT: pin {q.step}.{q.index} final key {kv.1.step}.{kv.1.index}"] }
          else
            st := { st with runValidPinNot := st.runValidPinNot + 1 }
            if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"RUN VALID, PIN NOT: pin {q.step}.{q.index} final key {kv.1.step}.{kv.1.index}"] }
          if pv && rv then
            match runState with
            | none => pure ()
            | some r =>
              let a : Std.HashSet PathNodeId := Std.HashSet.ofList (Fq.nodes.map (·.id))
              let b : Std.HashSet PathNodeId := Std.HashSet.ofList (r.nodes.map (·.id))
              let ea := Fq.nodes.filter (fun m => !b.contains m.id)
              let eb := r.nodes.filter (fun m => !a.contains m.id)
              if ea.isEmpty && eb.isEmpty then st := { st with nodesEqual := st.nodesEqual + 1 }
              st := { st with pinExtraNodes := st.pinExtraNodes + ea.length, runExtraNodes := st.runExtraNodes + eb.length }
              if (!ea.isEmpty || !eb.isEmpty) && st.ex.length < 8 then
                st := { st with ex := st.ex ++ [s!"NODE SETS DIFFER pin {q.step}.{q.index} key {kv.1.step}.{kv.1.index}: pin-only {ea.length} run-only {eb.length}"] }
              let ta : Std.HashMap PathNodeId (Std.HashSet PathNodeId) := Fq.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
              let tb : Std.HashMap PathNodeId (Std.HashSet PathNodeId) := r.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
              let mut xa := 0
              let mut xb := 0
              for m in Fq.nodes do
                match tb.get? m.id with
                | none => pure ()
                | some ob => for w in m.owners do if a.contains w && b.contains w && !ob.contains w then xa := xa + 1
              for m in r.nodes do
                match ta.get? m.id with
                | none => pure ()
                | some oa => for w in m.owners do if a.contains w && b.contains w && !oa.contains w then xb := xb + 1
              if xa == 0 && xb == 0 then st := { st with ownersEqual := st.ownersEqual + 1 }
              st := { st with pinExtraOwners := st.pinExtraOwners + xa, runExtraOwners := st.runExtraOwners + xb }
    return st

def reportK (name : String) (st : KStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} bothValid={st.bothValid} bothInvalid={st.bothInvalid} PIN_VALID_RUN_NOT={st.pinValidRunNot} RUN_VALID_PIN_NOT={st.runValidPinNot} | node sets equal={st.nodesEqual} pin-only nodes={st.pinExtraNodes} run-only nodes={st.runExtraNodes} | owner tables equal={st.ownersEqual} pin-only entries={st.pinExtraOwners} run-only entries={st.runExtraOwners} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

structure JStat where
  joins : Nat := 0
  constraints : Nat := 0
  joinValid : Nat := 0
  bothSidesInvalid : Nat := 0
  borrowedGowners : Nat := 0
  constraintsWithBorrow : Nat := 0
  gownersChecked : Nat := 0
  entriesChecked : Nat := 0
  borrowedEntries : Nat := 0
  sharedNodes : Nat := 0
  exclChoices : Nat := 0
  exclLost : Nat := 0
  sharedChoices : Nat := 0
  sharedLost : Nat := 0
  sharedKeptBoth : Nat := 0
  topOneSide : Nat := 0
  topBothSides : Nat := 0
  topSharedOnly : Nat := 0
  ex : List String := []

/-- Every join the Improves driver performs: under no pin and under every single pin of a step with a
choice, is every global owner of the pinned join a global owner of a pinned side? -/
def joinCensus (e h : GPathM) (st0 : JStat) : JStat := Id.run do
  let mut st := { st0 with joins := st0.joins + 1 }
  let J := join e h
  let J0 := filterAllAgg J []
  if !isValid J0 then return st
  let cs := J0.current_step
  let mut cands : List (List NodeId) := [[]]
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let ids := ((J0.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
    if ids.length > 1 then
      for q in ids do cands := cands ++ [[q]]
  let r1 : Std.HashSet PathNodeId := Std.HashSet.ofList e.gowners
  let r2 : Std.HashSet PathNodeId := Std.HashSet.ofList h.gowners
  let n1 : Std.HashSet PathNodeId := Std.HashSet.ofList (e.nodes.map (·.id))
  let n2 : Std.HashSet PathNodeId := Std.HashSet.ofList (h.nodes.map (·.id))
  for C in cands do
    st := { st with constraints := st.constraints + 1 }
    let FJ := filterAllAgg J C
    if !isValid FJ then continue
    st := { st with joinValid := st.joinValid + 1 }
    let F1 := filterAllAgg e C
    let F2 := filterAllAgg h C
    let g1 : Std.HashSet PathNodeId := if isValid F1 then Std.HashSet.ofList F1.gowners else {}
    let g2 : Std.HashSet PathNodeId := if isValid F2 then Std.HashSet.ofList F2.gowners else {}
    if !isValid F1 && !isValid F2 then
      st := { st with bothSidesInvalid := st.bothSidesInvalid + 1 }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"JOIN VALID, BOTH SIDES INVALID under {C.map (fun r => s!"{r.step}.{r.index}")} (cs {cs})"] }
    for m in FJ.nodes do
      if (n1.contains m.id) && (n2.contains m.id) then st := { st with sharedNodes := st.sharedNodes + 1 }
    -- the two top nodes of the join: same map node, different parents, one per side
    -- top-step nodes of the join, split by which side actually has them
    let topNodes := FJ.nodes.filter (fun m => m.id.id.step == cs - 1)
    let tops1 : List (Std.HashSet PathNodeId) :=
      (topNodes.filter (fun m => n1.contains m.id && !n2.contains m.id)).map
        (fun m => Std.HashSet.ofList m.owners)
    let tops2 : List (Std.HashSet PathNodeId) :=
      (topNodes.filter (fun m => n2.contains m.id && !n1.contains m.id)).map
        (fun m => Std.HashSet.ofList m.owners)
    let mut borrowed := 0
    for q in FJ.gowners do
      st := { st with gownersChecked := st.gownersChecked + 1 }
      -- which side had this choice before the join?
      let in1 := r1.contains q
      let in2 := r2.contains q
      -- does q own a top node exclusive to side 1? to side 2?
      let t1q := tops1.any (fun o => o.contains q)
      let t2q := tops2.any (fun o => o.contains q)
      if t1q && t2q then st := { st with topBothSides := st.topBothSides + 1 }
      else if t1q || t2q then st := { st with topOneSide := st.topOneSide + 1 }
      else st := { st with topSharedOnly := st.topSharedOnly + 1 }
      if in1 && in2 then
        st := { st with sharedChoices := st.sharedChoices + 1 }
        if g1.contains q && g2.contains q then
          st := { st with sharedKeptBoth := st.sharedKeptBoth + 1 }
        else if !g1.contains q && !g2.contains q then
          st := { st with sharedLost := st.sharedLost + 1 }
      else if in1 || in2 then
        st := { st with exclChoices := st.exclChoices + 1 }
        if !((in1 && g1.contains q) || (in2 && g2.contains q)) then
          st := { st with exclLost := st.exclLost + 1 }
          if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"EXCLUSIVE CHOICE LOST {showPid q} (side {if in1 then 1 else 2}) under {C.map (fun r => s!"{r.step}.{r.index}")}"] }
      if !g1.contains q && !g2.contains q then borrowed := borrowed + 1
    if borrowed > 0 then
      st := { st with borrowedGowners := st.borrowedGowners + borrowed, constraintsWithBorrow := st.constraintsWithBorrow + 1 }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"BORROWED {borrowed} gowners under {C.map (fun r => s!"{r.step}.{r.index}")} (cs {cs})"] }
  return st

-- ============================================================
-- The triple the `par` condition needs, at nodes with several parents
-- ============================================================

structure TStat where
  states : Nat := 0
  nodes : Nat := 0
  multiParent : Nat := 0
  checks : Nat := 0
  gaps : Nat := 0
  ex : List String := []

/-- At every node with more than one parent (the residue `ParentWitness.par_witness_triple`
leaves open), for every top node it owns and every owner it has: is some parent of the node an
owner of both? That is exactly the triple the `par` condition of a restricted support needs. -/
def tripleCensus (g : GPathM) (st0 : TStat) : TStat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let cs := g.current_step
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let tops : List PathNodeId := (g.nodes.filter (fun m => m.id.id.step == cs - 1)).map (·.id)
  for n in g.nodes do
    st := { st with nodes := st.nodes + 1 }
    if n.parents.length > 1 && n.id.id.step > 0 then
      st := { st with multiParent := st.multiParent + 1 }
      let no := tbl.getD n.id {}
      for z in tops do
        if no.contains z then
          let zo := tbl.getD z {}
          -- `par` is only needed inside the slice of the anchor: `v` must own `z` too
          for v in n.owners.filter (fun v => zo.contains v) do
            st := { st with checks := st.checks + 1 }
            let vo := tbl.getD v {}
            if !(n.parents.any (fun c => vo.contains c && zo.contains c)) then
              st := { st with gaps := st.gaps + 1 }
              if st.ex.length < 8 then
                st := { st with ex := st.ex ++
                  [s!"NO TRIPLE PARENT x={showPid n.id} v={showPid v} z={showPid z}"] }
  return st

def runTriples (φ : Cnf) (allLines : Bool) (st0 : TStat) : TStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let mut i := 0
  for line in lines do
    i := i + 1
    if allLines || i == n then
      for kv in line do
        let G := filterAllAgg kv.2 []
        if isValid G then st := tripleCensus G st
  return st

/-- The same census, but on the state the proof actually uses: the one with the anchor's map node
pinned. `par` is needed there, not in the unpinned state. -/
def runTriplesPinned (φ : Cnf) (st0 : TStat) : TStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  for line in lines do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then
        let cs := G.current_step
        let tops := ((G.nodes.filter (fun m => m.id.id.step == cs - 1)).map (·.id.id)).eraseDups
        for t in tops do
          let B := filterAllAgg G [t]
          if isValid B then st := tripleCensus B st
  return st

def reportT (name : String) (st : TStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} nodes={st.nodes} multiParent={st.multiParent} checks={st.checks} TRIPLE_GAPS={st.gaps} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- The entries the slice of a side's top node uses
-- ============================================================

structure SStat where
  joins : Nat := 0
  constraints : Nat := 0
  tops : Nat := 0
  sliceNodes : Nat := 0
  pairs : Nat := 0
  foreignPairs : Nat := 0
  ex : List String := []

/-- For each top node exclusive to one side of a join, take its slice in the constrained join and
check every owner pair inside it against **that side's own tables**: does the support of the slice
ever use an entry the side does not have? That is the entry half of `JoinSplit`. -/
def sliceCensus (e h : GPathM) (st0 : SStat) : SStat := Id.run do
  let mut st := { st0 with joins := st0.joins + 1 }
  let J := join e h
  let J0 := filterAllAgg J []
  if !isValid J0 then return st
  let cs := J0.current_step
  let t1 : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    e.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let t2 : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    h.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut cands : List (List NodeId) := [[]]
  for i in [0:cs.toNat] do
    let k : Int := Int.ofNat i
    let ids := ((J0.gowners.filter (fun q => q.id.step == k)).map (·.id)).eraseDups
    if ids.length > 1 then
      for q in ids do cands := cands ++ [[q]]
  for C in cands do
    let B := filterAllAgg J C
    if !isValid B then continue
    st := { st with constraints := st.constraints + 1 }
    let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
      B.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
    for m in B.nodes.filter (fun m => m.id.id.step == cs - 1) do
      -- which side has this top node, exclusively?
      let side1 := t1.contains m.id && !t2.contains m.id
      let side2 := t2.contains m.id && !t1.contains m.id
      if !(side1 || side2) then continue
      st := { st with tops := st.tops + 1 }
      let tside := if side1 then t1 else t2
      let slice : List PathNodeId :=
        (B.nodes.filter (fun n => (tbl.getD n.id {}).contains m.id)).map (·.id)
      let sliceSet : Std.HashSet PathNodeId := Std.HashSet.ofList slice
      st := { st with sliceNodes := st.sliceNodes + slice.length }
      for x in slice do
        let xo := tbl.getD x {}
        for v in xo.toList.filter (fun v => sliceSet.contains v) do
          st := { st with pairs := st.pairs + 1 }
          let own := (tside.getD x {}).contains v
          if !own then
            st := { st with foreignPairs := st.foreignPairs + 1 }
            if st.ex.length < 8 then
              st := { st with ex := st.ex ++
                [s!"FOREIGN ENTRY in slice of {showPid m.id} (side {if side1 then 1 else 2}): {showPid x} <- {showPid v}"] }
  return st

def runSlices (φ : Cnf) (st0 : SStat) : SStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let h := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid h then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) => if okJoin e h then st := sliceCensus e h st
          | none => pure ()
          next := insertPure next d h
    line := next
  return st

def reportS (name : String) (st : SStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} constraints={st.constraints} exclusiveTops={st.tops} sliceNodes={st.sliceNodes} pairs={st.pairs} FOREIGN_PAIRS={st.foreignPairs} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Transitivity of ownership on ordered triples
-- ============================================================

structure TrStat where
  states : Nat := 0
  nodes : Nat := 0
  triples : Nat := 0
  failures : Nat := 0
  truncated : Nat := 0
  ex : List String := []

/-- The induction step of the frontal attack on `NoDeadEnd`: if `a` owns `b` and `b` owns `c`, with
`a.step < b.step < c.step`, does `a` own `c`? With that, a partial chain extends by the owner the
pair consistency of its lowest pick already provides. -/
def transCensus (g : GPathM) (budget : Nat) (st0 : TrStat) : TrStat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut seen := 0
  for nb in g.nodes do
    st := { st with nodes := st.nodes + 1 }
    let b := nb.id
    -- c above b owning b, a below b owned by b
    for c in nb.owners.filter (fun c => c.id.step > b.id.step) do
      let co := tbl.getD c {}
      if !co.contains b then continue
      for a in nb.owners.filter (fun a => a.id.step < b.id.step) do
        if seen > budget then
          st := { st with truncated := st.truncated + 1 }
          return st
        seen := seen + 1
        st := { st with triples := st.triples + 1 }
        if !co.contains a then
          st := { st with failures := st.failures + 1 }
          if st.ex.length < 8 then
            st := { st with ex := st.ex ++
              [s!"NOT TRANSITIVE a={showPid a} b={showPid b} c={showPid c}"] }
  return st

def runTrans (φ : Cnf) (allLines : Bool) (budget : Nat) (st0 : TrStat) : TrStat := Id.run do
  let lines := aggLines φ
  let n := lines.length
  let mut st := st0
  let mut i := 0
  for line in lines do
    i := i + 1
    if allLines || i == n then
      for kv in line do
        let G := filterAllAgg kv.2 []
        if isValid G then st := transCensus G budget st
  return st

def reportTr (name : String) (st : TrStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} nodes={st.nodes} triples={st.triples} NOT_TRANSITIVE={st.failures} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- No dead ends, measured directly
-- ============================================================

structure DStat where
  states : Nat := 0
  anchors : Nat := 0
  extensions : Nat := 0
  full : Nat := 0
  deadEnds : Nat := 0
  truncated : Nat := 0
  ex : List String := []

/-- `NoDeadEnd`, measured as it is stated: every partial chain from the top step down extends by
one pick. Explores every partial chain (the property is universal), under a budget. -/
partial def deadWalk (g : GPathM) (tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId))
    (chain : List PathNodeId) (lo : Int) (st0 : DStat) (budget : Nat) : DStat × Nat := Id.run do
  let mut st := st0
  let mut bud := budget
  if lo == 0 then
    return ({ st with full := st.full + 1 }, bud)
  let x := chain.head!
  let parents := match g.node? x with | some n => n.parents | none => []
  let cands := parents.filter (fun c =>
    c.id.step == lo - 1
    && (match g.node? c with | some _ => true | none => false)
    && chain.all (fun y => (tbl.getD y {}).contains c)
    && g.gowners.contains c
    && (tbl.getD c {}).contains c
    && (if lo - 1 == 0 then c.parent_id.isNone else !c.parent_id.isNone))
  if cands.isEmpty then
    st := { st with deadEnds := st.deadEnds + 1 }
    if st.ex.length < 6 then
      st := { st with ex := st.ex ++
        [s!"DEAD END at step {lo - 1} under chain {chain.map showPid}"] }
    return (st, bud)
  for c in cands do
    if bud == 0 then
      return ({ st with truncated := st.truncated + 1 }, 0)
    bud := bud - 1
    st := { st with extensions := st.extensions + 1 }
    let (st', bud') := deadWalk g tbl (c :: chain) (lo - 1) st bud
    st := st'
    bud := bud'
  return (st, bud)

def deadCensus (g : GPathM) (budget : Nat) (st0 : DStat) : DStat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let cs := g.current_step
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut bud := budget
  for n in g.nodes.filter (fun n => n.id.id.step == cs - 1) do
    let q := n.id
    if !(g.gowners.contains q && (tbl.getD q {}).contains q) then continue
    if !(if cs - 1 == 0 then q.parent_id.isNone else !q.parent_id.isNone) then continue
    st := { st with anchors := st.anchors + 1 }
    let (st', bud') := deadWalk g tbl [q] (cs - 1) st bud
    st := st'
    bud := bud'
  return st

def runDead (φ : Cnf) (budget : Nat) (st0 : DStat) : DStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  for line in lines do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := deadCensus G budget st
  return st

def reportD (name : String) (st : DStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} anchors={st.anchors} extensions={st.extensions} fullChains={st.full} DEAD_ENDS={st.deadEnds} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

/-- The Improves driver, with every join inspected. -/
def runJoins (φ : Cnf) (st0 : JStat) : JStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let h := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid h then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e h then st := joinCensus e h st
          | none => pure ()
          next := insertPure next d h
    line := next
  return st

def reportJ (name : String) (st : JStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} constraints={st.constraints} joinValid={st.joinValid} BOTH_SIDES_INVALID={st.bothSidesInvalid} gownersChecked={st.gownersChecked} BORROWED_GOWNERS={st.borrowedGowners} (in {st.constraintsWithBorrow} constraints) | sharedNodes={st.sharedNodes} exclusive={st.exclChoices} EXCLUSIVE_LOST={st.exclLost} shared={st.sharedChoices} SHARED_LOST={st.sharedLost} sharedKeptBoth={st.sharedKeptBoth} topOneSide={st.topOneSide} TOP_BOTH_SIDES={st.topBothSides} topSharedOnly={st.topSharedOnly} | {ms}ms"
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
  | "spc" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSpc φ {})
        let t1 ← IO.monoMsNow
        IO.println s!"spc {path}: pins={st.pins} carriers(1,2,3,4,5+)={st.carriers.toList.drop 1} | interior E pairs={st.ePairsInterior} nonSPC={st.nonSpcInterior} (fail only at pinned step {st.failOnlyAtPinned}) SPC={st.spcInterior} | triangles={st.triangles} TRIANGLE_FAIL={st.triangleFail} | cells={st.cells} CELLS_NO_HALF={st.cellsNoHalf} witnesses={st.witnesses} both={st.witBoth} xOnly={st.witXonly} vOnly={st.witVonly} none={st.witNone} | boundaryPins={st.boundaryPins} xOnly with boundary pin={st.badPinBoundary} | failing steps of SPC v z: atPinned={st.badAtPinned} between={st.badBetween} outside={st.badOutside} atStep0orTop={st.badAtBoundaryStep} distOutside(0..7+)={st.badDist.toList} | {t1 - t0}ms"
        for e in st.ex do IO.println s!"  EX {e}"
  | "joins" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : JStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runJoins φ st
      let t1 ← IO.monoMsNow
      reportJ s!"joins seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "triples" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : TStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runTriples φ true st
      let t1 ← IO.monoMsNow
      reportT s!"triples seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "dead" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runDead φ 200000 {})
        let t1 ← IO.monoMsNow
        reportD s!"dead {path}" st (t1 - t0)
  | "trans" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runTrans φ true 3000000 {})
        let t1 ← IO.monoMsNow
        reportTr s!"trans {path}" st (t1 - t0)
  | "slices" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSlices φ {})
        let t1 ← IO.monoMsNow
        reportS s!"slices {path}" st (t1 - t0)
  | "triplesPin" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runTriplesPinned φ {})
        let t1 ← IO.monoMsNow
        reportT s!"triplesPin {path}" st (t1 - t0)
  | "triples" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runTriples φ true {})
        let t1 ← IO.monoMsNow
        reportT s!"triples {path}" st (t1 - t0)
  | "joins" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runJoins φ {})
        let t1 ← IO.monoMsNow
        reportJ s!"joins {path}" st (t1 - t0)
  | "commute" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : KStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runCommute φ st
      let t1 ← IO.monoMsNow
      reportK s!"commute seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "commute" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runCommute φ {})
        let t1 ← IO.monoMsNow
        reportK s!"commute {path}" st (t1 - t0)
  | "chains" :: mode :: walks :: depth :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runChains φ (mode == "all") walks.toNat! depth.toNat! 17 {})
        let t1 ← IO.monoMsNow
        reportC s!"chains {mode} {path} (walks {walks}, depth {depth})" st (t1 - t0)
  | "chainsr" :: mode :: walks :: depth :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : CStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runChains φ (mode == "all") walks.toNat! depth.toNat! seed st
      let t1 ← IO.monoMsNow
      reportC s!"chains {mode} seed {seed} ({cases} formulas, {nvMin}+ vars, walks {walks}, depth {depth})" st (t1 - t0)
  | "walk" :: "all" :: walks :: seed :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runWalkAll φ walks.toNat! seed.toNat! {})
        let t1 ← IO.monoMsNow
        reportW s!"walk all lines {path}" st (t1 - t0)
  | "walk" :: "random" :: walks :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : WStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runWalk φ walks.toNat! seed st
      let t1 ← IO.monoMsNow
      reportW s!"walk seed {seed} ({cases} formulas, {nvMin}+ vars, {walks} walks per state)" st (t1 - t0)
  | "walk" :: walks :: seed :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runWalk φ walks.toNat! seed.toNat! {})
        let t1 ← IO.monoMsNow
        reportW s!"walk {path}" st (t1 - t0)
  | "depth2" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runDepth2 φ {})
        let t1 ← IO.monoMsNow
        IO.println s!"depth2 {path}: first pins={st.firstPins} second pins={st.secondPins} INVALID={st.invalid} slice nodes={st.sliceNodes} SLICE_REMOVED={st.sliceRemoved} (second pin on step 0/top {st.removedBoundaryPin}, interior {st.removedInteriorPin}; in {st.pinsRemoving} pins; interior second pins {st.interiorSecondPins}; removed nodes' steps {st.removedSteps}) OUTSIDE_KEPT={st.outsideKept} | base double-slice nodes alive after a that lost every b carrier={st.lostCarrier} | {t1 - t0}ms"
        for e in st.ex do IO.println s!"  EX {e}"
  | "pins2" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPins2 φ {})
        let t1 ← IO.monoMsNow
        IO.println s!"pins2 {path}: pairs={st.pairs} valid={st.valid} invalid={st.invalid} (double slice present at every step {st.invalidWithFullSlice}, some step empty {st.invalidSliceEmptyStep}) | valid: SLICE_REMOVED={st.sliceRemoved} OUTSIDE_KEPT={st.outsideKept} SEQUENTIAL_DIFFERS={st.seqDiffers} | {t1 - t0}ms"
        for e in st.ex do IO.println s!"  EX {e}"
  | "hered" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : HerStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runHered φ st
      let t1 ← IO.monoMsNow
      IO.println s!"hered seed {seed} ({cases} formulas, {nvMin}+ vars): pins={st.pins} interior SPC pairs={st.r1Pairs} witnesses={st.witnesses} BAD={st.badWitnesses} CELLS_WITHOUT_GOOD_WITNESS={st.cellsNoGood} | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "hered" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runHered φ {})
        let t1 ← IO.monoMsNow
        IO.println s!"hered {path}: pins={st.pins} interior SPC pairs={st.r1Pairs} witnesses={st.witnesses} BAD={st.badWitnesses} (boundary z {st.badBoundaryZ}) CELLS_WITHOUT_GOOD_WITNESS={st.cellsNoGood} | {t1 - t0}ms"
        for e in st.ex do IO.println s!"  EX {e}"
  | "rounds" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : RStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runRounds φ st
      let t1 ← IO.monoMsNow
      reportR s!"rounds seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "rounds" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runRounds φ {})
        let t1 ← IO.monoMsNow
        reportR s!"rounds {path}" st (t1 - t0)
  | "gfpE" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : GStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runGfp false φ false st
      let t1 ← IO.monoMsNow
      reportG s!"gfpE seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "gfpE" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runGfp false φ false {})
        let t1 ← IO.monoMsNow
        reportG s!"gfpE {path}" st (t1 - t0)
  | "gfp" :: "all" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runGfp true φ true {})
        let t1 ← IO.monoMsNow
        reportG s!"gfp {path} [all lines]" st (t1 - t0)
  | "gfp" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : GStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runGfp true φ false st
      let t1 ← IO.monoMsNow
      reportG s!"gfp seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "gfp" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runGfp true φ false {})
        let t1 ← IO.monoMsNow
        reportG s!"gfp {path}" st (t1 - t0)
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
