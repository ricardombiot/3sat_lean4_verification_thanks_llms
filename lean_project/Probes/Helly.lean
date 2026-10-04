import AbsSat.Cnf.Dimacs
import AbsSat.SatMachine.DiffTest
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.PureDriverImproves
import AbsSat.GraphPath.Model.Answer
import AbsSat.GraphPath.Model.ImprovesCima
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

instance : _root_.Inhabited NodeId := ⟨{ step := 0, index := 0 }⟩

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
      -- only the ADJACENT case: `a` a parent of `b`, which is what the descent needs
      for a in nb.parents do
        if seen > budget then
          st := { st with truncated := st.truncated + 1 }
          return st
        seen := seen + 1
        st := { st with triples := st.triples + 1 }
        if !co.contains a then
          st := { st with failures := st.failures + 1 }
          if st.ex.length < 8 then
            st := { st with ex := st.ex ++
              [s!"PARENT NOT TRANSITIVE a={showPid a} b={showPid b} c={showPid c}"] }
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
  IO.println s!"{name}: states={st.states} nodes={st.nodes} parentTriples={st.triples} PARENT_NOT_TRANSITIVE={st.failures} truncated={st.truncated} | {ms}ms"
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
  nearChecks : Nat := 0
  nearNotEnough : Nat := 0
  nestChecks : Nat := 0
  NEST_FAILS : Nat := 0
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
  let base := parents.filter (fun c =>
    c.id.step == lo - 1
    && (match g.node? c with | some _ => true | none => false)
    && g.gowners.contains c
    && (tbl.getD c {}).contains c
    && (if lo - 1 == 0 then c.parent_id.isNone else !c.parent_id.isNone))
  let cands := base.filter (fun c => chain.all (fun y => (tbl.getD y {}).contains c))
  -- are the candidate sets NESTED along the chain? (a candidate good for a higher pick should be
  -- good for the lower ones; then the intersection is the anchor's set, non-empty by pairs)
  let picks := chain  -- head is the lowest pick
  for (ylow, i) in picks.zipIdx do
    for yhigh in (picks.drop (i + 1)) do
      for c in base do
        if (tbl.getD yhigh {}).contains c then
          st := { st with nestChecks := st.nestChecks + 1 }
          if !(tbl.getD ylow {}).contains c then
            st := { st with NEST_FAILS := st.NEST_FAILS + 1 }
            if st.ex.length < 6 then
              st := { st with ex := st.ex ++
                [s!"NOT NESTED at step {lo - 1}: c={showPid c} ok for {showPid yhigh} but not for {showPid ylow}"] }
  -- does the pick immediately above already decide the parent?
  match chain with
  | _ :: y :: _ =>
    let near := base.filter (fun c => (tbl.getD y {}).contains c)
    st := { st with nearChecks := st.nearChecks + near.length }
    let bad := near.filter (fun c => !cands.contains c)
    if !bad.isEmpty then
      st := { st with nearNotEnough := st.nearNotEnough + bad.length }
      if st.ex.length < 6 then
        st := { st with ex := st.ex ++
          [s!"NEAR NOT ENOUGH at step {lo - 1}: {bad.map showPid} accepted by {showPid y} but not by the chain {chain.map showPid}"] }
  | _ => pure ()
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
  IO.println s!"{name}: states={st.states} anchors={st.anchors} extensions={st.extensions} fullChains={st.full} DEAD_ENDS={st.deadEnds} nearChecks={st.nearChecks} NEAR_NOT_ENOUGH={st.nearNotEnough} nestChecks={st.nestChecks} NEST_FAILS={st.NEST_FAILS} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- JoinCoveredF: is a partial chain of a join a chain of one side?
-- ============================================================

structure CovStat where
  joins : Nat := 0
  chains : Nat := 0
  oneSide : Nat := 0
  mixed : Nat := 0
  mixedExtends : Nat := 0
  MIXED_STUCK : Nat := 0
  truncated : Nat := 0
  ex : List String := []

/-- Is this partial chain (lowest pick first) entirely a chain of `side`? -/
def chainInSide (side : GPathM) (tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId))
    (gow : Std.HashSet PathNodeId) (chain : List PathNodeId) : Bool :=
  chain.all (fun x =>
    (match side.node? x with | some _ => true | none => false)
    && gow.contains x
    && (tbl.getD x {}).contains x
    && chain.all (fun y => x == y || (tbl.getD y {}).contains x))
  && (chain.zip (chain.drop 1)).all (fun (lo, hi) =>
    (match side.node? hi with | some n => n.parents.contains lo | none => false)
    && (match side.node? lo with | some n => n.sons.contains hi | none => false))

/-- Walk every partial chain of the join and classify it. -/
partial def coverWalk (J e h : GPathM)
    (tJ tE tH : Std.HashMap PathNodeId (Std.HashSet PathNodeId))
    (gE gH : Std.HashSet PathNodeId) (chain : List PathNodeId) (lo : Int)
    (st0 : CovStat) (budget : Nat) : CovStat × Nat := Id.run do
  let mut st := st0
  let mut bud := budget
  st := { st with chains := st.chains + 1 }
  -- classify this partial chain
  if chainInSide e tE gE chain || chainInSide h tH gH chain then
    st := { st with oneSide := st.oneSide + 1 }
  else
    st := { st with mixed := st.mixed + 1 }
  if lo == 0 then
    return (st, bud)
  let x := chain.head!
  let parents := match J.node? x with | some n => n.parents | none => []
  let cands := parents.filter (fun c =>
    c.id.step == lo - 1
    && (match J.node? c with | some _ => true | none => false)
    && chain.all (fun y => (tJ.getD y {}).contains c)
    && J.gowners.contains c
    && (tJ.getD c {}).contains c
    && (if lo - 1 == 0 then c.parent_id.isNone else !c.parent_id.isNone))
  -- a mixed chain that cannot extend in the join is the counterexample to look for
  if !(chainInSide e tE gE chain || chainInSide h tH gH chain) then
    if cands.isEmpty then
      st := { st with MIXED_STUCK := st.MIXED_STUCK + 1 }
      if st.ex.length < 6 then
        st := { st with ex := st.ex ++ [s!"MIXED STUCK at step {lo - 1}: {chain.map showPid}"] }
    else
      st := { st with mixedExtends := st.mixedExtends + 1 }
  for c in cands do
    if bud == 0 then
      return ({ st with truncated := st.truncated + 1 }, 0)
    bud := bud - 1
    let (st', bud') := coverWalk J e h tJ tE tH gE gH (c :: chain) (lo - 1) st bud
    st := st'
    bud := bud'
  return (st, bud)

def coverCensus (e h : GPathM) (budget : Nat) (st0 : CovStat) : CovStat := Id.run do
  let mut st := { st0 with joins := st0.joins + 1 }
  let J := filterAllAgg (join e h) []
  if !isValid J then return st
  let cs := J.current_step
  let mk (g : GPathM) : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let tJ := mk J
  let tE := mk e
  let tH := mk h
  let gE : Std.HashSet PathNodeId := Std.HashSet.ofList e.gowners
  let gH : Std.HashSet PathNodeId := Std.HashSet.ofList h.gowners
  let mut bud := budget
  for n in J.nodes.filter (fun n => n.id.id.step == cs - 1) do
    let q := n.id
    if !(J.gowners.contains q && (tJ.getD q {}).contains q) then continue
    if !(if cs - 1 == 0 then q.parent_id.isNone else !q.parent_id.isNone) then continue
    let (st', bud') := coverWalk J e h tJ tE tH gE gH [q] (cs - 1) st bud
    st := st'
    bud := bud'
  return st

def runCover (φ : Cnf) (budget : Nat) (st0 : CovStat) : CovStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) => if okJoin e hst then st := coverCensus e hst budget st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportCov (name : String) (st : CovStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} chains={st.chains} oneSide={st.oneSide} mixed={st.mixed} mixedExtends={st.mixedExtends} MIXED_STUCK={st.MIXED_STUCK} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Is the slice of a node a clique?
-- ============================================================

structure QStat where
  states : Nat := 0
  pairs : Nat := 0
  failures : Nat := 0
  topPairs : Nat := 0
  topFailures : Nat := 0
  truncated : Nat := 0
  ex : List String := []

/-- For every node, are two of its owners compatible with each other? If the slice of a node is a
clique, the descent needs no k-consistency: the anchor is the common witness. Counted for every
node and, separately, for the nodes of the top step (the anchors). -/
def cliqueCensus (g : GPathM) (budget : Nat) (st0 : QStat) : QStat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let cs := g.current_step
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut seen := 0
  for d in g.nodes do
    let isTop := d.id.id.step == cs - 1
    for a in d.owners do
      for b in d.owners.filter (fun b => b.id.step > a.id.step) do
        if seen > budget then
          st := { st with truncated := st.truncated + 1 }
          return st
        seen := seen + 1
        let ok := (tbl.getD b {}).contains a
        st := { st with pairs := st.pairs + 1 }
        if isTop then st := { st with topPairs := st.topPairs + 1 }
        if !ok then
          st := { st with failures := st.failures + 1 }
          if isTop then st := { st with topFailures := st.topFailures + 1 }
          if st.ex.length < 6 then
            st := { st with ex := st.ex ++
              [s!"SLICE NOT CLIQUE d={showPid d.id}{if isTop then " (TOP)" else ""} a={showPid a} b={showPid b}"] }
  return st

def runClique (φ : Cnf) (budget : Nat) (st0 : QStat) : QStat := Id.run do
  let lines := aggLines φ
  let mut st := st0
  for line in lines do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if isValid G then st := cliqueCensus G budget st
  return st

def reportQ (name : String) (st : QStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} pairs={st.pairs} NOT_CLIQUE={st.failures} | topPairs={st.topPairs} TOP_NOT_CLIQUE={st.topFailures} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

/-- The Improves driver, with every join inspected. -/
-- ============================================================
-- Keys and futures (v137): do two states with the same key see the same future?
-- ============================================================

structure FStat where
  joins : Nat := 0
  noFuture : Nat := 0          -- the future asks nothing of the past
  sameFuture : Nat := 0        -- both sides project the same pasts onto the future's steps
  nested : Nat := 0            -- one side's projections contain the other's
  differ : Nat := 0            -- neither contains the other
  projE : Nat := 0
  projH : Nat := 0
  projJ : Nat := 0
  JOIN_SPURIOUS : Nat := 0     -- projections of the join that neither side has
  relSteps : Nat := 0
  pastSteps : Nat := 0
  truncated : Nat := 0
  sigSame : Nat := 0           -- both sides admit the same maximal sets of future nodes
  sigNested : Nat := 0
  sigDiffer : Nat := 0
  sigE : Nat := 0
  sigH : Nat := 0
  futNodes : Nat := 0
  exSig : List String := []
  ex : List String := []

/-- Every complete chain of `g` (lowest pick first), with the reader's candidate rule. -/
partial def fullChains (g : GPathM) (tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId))
    (chain : List PathNodeId) (lo : Int) (acc : Array (List PathNodeId)) (budget : Nat) :
    Array (List PathNodeId) × Nat := Id.run do
  if lo == 0 then return (acc.push chain, budget)
  let x := chain.head!
  let parents := match g.node? x with | some n => n.parents | none => []
  let cands := parents.filter (fun c =>
    c.id.step == lo - 1
    && (match g.node? c with | some _ => true | none => false)
    && chain.all (fun y => (tbl.getD y {}).contains c)
    && g.gowners.contains c
    && (tbl.getD c {}).contains c
    && (if lo - 1 == 0 then c.parent_id.isNone else !c.parent_id.isNone))
  let mut acc := acc
  let mut bud := budget
  for c in cands do
    if bud == 0 then return (acc, 0)
    bud := bud - 1
    let (a', b') := fullChains g tbl (c :: chain) (lo - 1) acc bud
    acc := a'
    bud := b'
  return (acc, bud)

/-- The complete chains of a state, as arrays of map nodes indexed by step; `none` if truncated. -/
def pasts (g : GPathM) (budget : Nat) : Option (Array (Array NodeId)) := Id.run do
  let cs := g.current_step
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut acc : Array (List PathNodeId) := #[]
  let mut bud := budget
  for n in g.nodes.filter (fun n => n.id.id.step == cs - 1) do
    let q := n.id
    if !(g.gowners.contains q && (tbl.getD q {}).contains q) then continue
    if !(if cs - 1 == 0 then q.parent_id.isNone else !q.parent_id.isNone) then continue
    let (a', b') := fullChains g tbl [q] (cs - 1) acc bud
    acc := a'
    bud := b'
    if bud == 0 then return none
  return some (acc.map (fun ch => ch.toArray.map (·.id)))

/-- The future map nodes (reachable from `d`) a past admits: all their backward requirements, hard
and weak, are met by it. -/
def signature (φ : Cnf) (cs : Int) (fut : List NodeId) (p : Array NodeId) : List NodeId :=
  fut.filter (fun y =>
    (reqOfCnf φ y).all (fun r => !(0 ≤ r.step && r.step < cs) || p.getD r.step.toNat ⟨-1, -1⟩ == r)
    && (weakReqOfCnf φ y).all (fun w => !(0 ≤ w.1 && w.1 < cs) || w.2.contains (p.getD w.1.toNat ⟨-1, -1⟩)))

/-- Keep only the maximal sets of a family (by inclusion). -/
def maximal (fam : List (List NodeId)) : Std.HashSet (List NodeId) := Id.run do
  let uniq := (Std.HashSet.ofList fam).toList
  let mut out : Std.HashSet (List NodeId) := {}
  for a in uniq do
    if !(uniq.any (fun b => b != a && a.all b.contains)) then out := out.insert a
  return out

def futureNodes (φ : Cnf) (d : NodeId) : List NodeId := Id.run do
  let last := stepCount φ - 1
  let mut frontier : List NodeId := [d]
  let mut out : List NodeId := []
  let mut k := d.step
  while k < last do
    let mut nxt : Std.HashSet NodeId := {}
    for x in frontier do
      for y in mapSons φ x.step x.index do nxt := nxt.insert y
    frontier := nxt.toList
    out := out ++ frontier
    k := k + 1
  return out

/-- The projections of a state's complete chains onto the steps `rel`; `none` if truncated. -/
def projections (g : GPathM) (rel : List Int) (budget : Nat) : Option (Std.HashSet (List NodeId)) := Id.run do
  let cs := g.current_step
  let tbl : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    g.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut acc : Array (List PathNodeId) := #[]
  let mut bud := budget
  for n in g.nodes.filter (fun n => n.id.id.step == cs - 1) do
    let q := n.id
    if !(g.gowners.contains q && (tbl.getD q {}).contains q) then continue
    if !(if cs - 1 == 0 then q.parent_id.isNone else !q.parent_id.isNone) then continue
    let (a', b') := fullChains g tbl [q] (cs - 1) acc bud
    acc := a'
    bud := b'
    if bud == 0 then return none
  let mut out : Std.HashSet (List NodeId) := {}
  for ch in acc do
    let arr := ch.toArray
    out := out.insert (rel.map (fun k => (arr[k.toNat]!).id))
  return some out

/-- The past steps the future of key `d` asks about: the requirements (hard and weak) of every map
node reachable from `d`, restricted to steps below `cs`. -/
def futureSteps (φ : Cnf) (d : NodeId) (cs : Int) : List Int := Id.run do
  let last := stepCount φ - 1
  let mut frontier : List NodeId := [d]
  let mut steps : Std.HashSet Int := {}
  let mut k := d.step
  while k < last do
    let mut nxt : Std.HashSet NodeId := {}
    for x in frontier do
      for y in mapSons φ x.step x.index do nxt := nxt.insert y
    frontier := nxt.toList
    for y in frontier do
      for r in reqOfCnf φ y do
        if r.step < cs && 0 ≤ r.step then steps := steps.insert r.step
      for w in weakReqOfCnf φ y do
        if w.1 < cs && 0 ≤ w.1 then steps := steps.insert w.1
    k := k + 1
  return (steps.toList.toArray.qsort (· < ·)).toList

def futureCensus (φ : Cnf) (d : NodeId) (e h : GPathM) (budget : Nat) (st0 : FStat) : FStat := Id.run do
  let mut st := { st0 with joins := st0.joins + 1 }
  let cs := e.current_step
  let rel := futureSteps φ d cs
  st := { st with relSteps := st.relSteps + rel.length, pastSteps := st.pastSteps + cs.toNat }
  let J := filterAllAgg (join e h) []
  match projections e rel budget, projections h rel budget, projections J rel budget with
  | some pe, some ph, some pj =>
    st := { st with projE := st.projE + pe.size, projH := st.projH + ph.size, projJ := st.projJ + pj.size }
    let spurious := pj.toList.filter (fun p => !(pe.contains p || ph.contains p))
    if !spurious.isEmpty then
      st := { st with JOIN_SPURIOUS := st.JOIN_SPURIOUS + spurious.length }
    if rel.isEmpty then
      st := { st with noFuture := st.noFuture + 1 }
    else
      let eh := pe.toList.all ph.contains
      let he := ph.toList.all pe.contains
      if eh && he then st := { st with sameFuture := st.sameFuture + 1 }
      else if eh || he then st := { st with nested := st.nested + 1 }
      else
        st := { st with differ := st.differ + 1 }
        if st.ex.length < 4 then
          st := { st with ex := st.ex ++ [s!"DIFFER key {d.step}:{d.index} cs={cs} rel={rel} |E|={pe.size} |H|={ph.size} |E∩H|={(pe.toList.filter ph.contains).length}"] }
  | _, _, _ => st := { st with truncated := st.truncated + 1 }
  -- finer: the maximal sets of future nodes each side's pasts admit
  let fut := futureNodes φ d
  match pasts e budget, pasts h budget with
  | some qe, some qh =>
    let me := maximal (qe.toList.map (signature φ cs fut))
    let mh := maximal (qh.toList.map (signature φ cs fut))
    st := { st with sigE := st.sigE + me.size, sigH := st.sigH + mh.size, futNodes := st.futNodes + fut.length }
    -- a side's future is the down-closure of its maximal sets; compare down-closures
    let covers (A B : Std.HashSet (List NodeId)) : Bool :=
      B.toList.all (fun b => A.toList.any (fun a => b.all a.contains))
    let eh := covers me mh
    let he := covers mh me
    if eh && he then st := { st with sigSame := st.sigSame + 1 }
    else if eh || he then st := { st with sigNested := st.sigNested + 1 }
    else
      st := { st with sigDiffer := st.sigDiffer + 1 }
      if st.exSig.length < 4 then
        st := { st with exSig := st.exSig ++ [s!"SIG DIFFER key {d.step}:{d.index} cs={cs} fut={fut.length} maxE={me.size} maxH={mh.size}"] }
  | _, _ => pure ()
  return st

def runFutures (φ : Cnf) (budget : Nat) (st0 : FStat) : FStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) => if okJoin e hst then st := futureCensus φ d e hst budget st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportF (name : String) (st : FStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} noFuture={st.noFuture} sameFuture={st.sameFuture} nested={st.nested} differ={st.differ} truncated={st.truncated} | relSteps/pastSteps={st.relSteps}/{st.pastSteps} | projections E={st.projE} H={st.projH} J={st.projJ} JOIN_SPURIOUS={st.JOIN_SPURIOUS} | signatures: same={st.sigSame} nested={st.sigNested} differ={st.sigDiffer} maxE={st.sigE} maxH={st.sigH} futNodes={st.futNodes} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"
  for e in st.exSig do IO.println s!"  EX {e}"

-- ============================================================
-- Nested joins (v138): are joins whose futures nest harmless for the descent?
-- ============================================================

/-- The future class of a join: 0 same, 1 nested, 2 differ; `none` if truncated. -/
def futureClass (φ : Cnf) (d : NodeId) (e h : GPathM) (budget : Nat) : Option Nat := Id.run do
  let cs := e.current_step
  let fut := futureNodes φ d
  match pasts e budget, pasts h budget with
  | some qe, some qh =>
    let me := maximal (qe.toList.map (signature φ cs fut))
    let mh := maximal (qh.toList.map (signature φ cs fut))
    let covers (A B : Std.HashSet (List NodeId)) : Bool :=
      B.toList.all (fun b => A.toList.any (fun a => b.all a.contains))
    let eh := covers me mh
    let he := covers mh me
    return some (if eh && he then 0 else if eh || he then 1 else 2)
  | _, _ => return none

structure NStat where
  byClass : Array DStat := #[{}, {}, {}]
  joins : Array Nat := #[0, 0, 0]
  truncated : Nat := 0

def runNested (φ : Cnf) (budget : Nat) (st0 : NStat) : NStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              match futureClass φ d e hst budget with
              | none => st := { st with truncated := st.truncated + 1 }
              | some c =>
                let J := filterAllAgg (join e hst) []
                st := { st with joins := st.joins.modify c (· + 1) }
                if isValid J then
                  st := { st with byClass := st.byClass.modify c (fun ds => deadCensus J budget ds) }
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportN (name : String) (st : NStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: truncated={st.truncated} | {ms}ms"
  for (lbl, i) in [("same", 0), ("nested", 1), ("differ", 2)] do
    let d := st.byClass.getD i {}
    IO.println s!"  {lbl}: joins={st.joins.getD i 0} extensions={d.extensions} full={d.full} DEAD_ENDS={d.deadEnds} near={d.nearChecks} NEAR_NOT_ENOUGH={d.nearNotEnough} nest={d.nestChecks} NEST_FAILS={d.NEST_FAILS} truncated={d.truncated}"

-- ============================================================
-- Distributivity (v138): does the send (weak filter, pins, review, up) distribute over the join?
-- ============================================================

structure DiStat where
  joins : Nat := 0
  sends : Nat := 0
  bothDead : Nat := 0
  oneAlive : Nat := 0
  bothAlive : Nat := 0
  VALIDITY_DIFFERS : Nat := 0
  equal : Nat := 0
  DIFFER : Nat := 0
  extraNodes : Nat := 0       -- nodes of F(join) not in join(F e, F h)
  missingNodes : Nat := 0
  extraOwners : Nat := 0      -- owner entries of F(join) not in join(F e, F h): borrowing
  missingOwners : Nat := 0
  extraGow : Nat := 0
  missingGow : Nat := 0
  ex : List String := []

/-- Compare two states as sets: nodes, owners per node, and global owners. -/
def diffStates (a b : GPathM) : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let tb : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    b.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let ta : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
    a.nodes.foldl (fun acc m => acc.insert m.id (Std.HashSet.ofList m.owners)) {}
  let mut xn := 0
  let mut mn := 0
  let mut xo := 0
  let mut mo := 0
  for m in a.nodes do
    match tb.get? m.id with
    | none => xn := xn + 1
    | some ob => for w in m.owners.eraseDups do if !ob.contains w then xo := xo + 1
  for m in b.nodes do
    match ta.get? m.id with
    | none => mn := mn + 1
    | some oa => for w in m.owners.eraseDups do if !oa.contains w then mo := mo + 1
  let ga := Std.HashSet.ofList a.gowners
  let gb := Std.HashSet.ofList b.gowners
  let xg := (a.gowners.eraseDups.filter (fun q => !gb.contains q)).length
  let mg := (b.gowners.eraseDups.filter (fun q => !ga.contains q)).length
  return (xn, mn, xo, mo, xg, mg)

def distribCheck (tag : String) (FJ Fe Fh : GPathM) (st0 : DiStat) : DiStat := Id.run do
  let mut st := { st0 with sends := st0.sends + 1 }
  let vj := isValid FJ
  let ve := isValid Fe
  let vh := isValid Fh
  let rhs : Option GPathM :=
    if ve && vh then some (join Fe Fh) else if ve then some Fe else if vh then some Fh else none
  if !ve && !vh then st := { st with bothDead := st.bothDead + 1 }
  else if ve && vh then st := { st with bothAlive := st.bothAlive + 1 }
  else st := { st with oneAlive := st.oneAlive + 1 }
  match rhs with
  | none =>
    if vj then
      st := { st with VALIDITY_DIFFERS := st.VALIDITY_DIFFERS + 1 }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"{tag}: join survives, both sides die"] }
  | some r =>
    if !vj then
      st := { st with VALIDITY_DIFFERS := st.VALIDITY_DIFFERS + 1 }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"{tag}: a side survives, the join dies"] }
    else
      let (xn, mn, xo, mo, xg, mg) := diffStates FJ r
      if xn + mn + xo + mo + xg + mg == 0 then st := { st with equal := st.equal + 1 }
      else
        st := { st with DIFFER := st.DIFFER + 1 }
        if st.ex.length < 8 then
          st := { st with ex := st.ex ++ [s!"{tag}: extraNodes={xn} missingNodes={mn} extraOwners={xo} missingOwners={mo} extraGow={xg} missingGow={mg}"] }
      st := { st with extraNodes := st.extraNodes + xn }
      st := { st with missingNodes := st.missingNodes + mn }
      st := { st with extraOwners := st.extraOwners + xo }
      st := { st with missingOwners := st.missingOwners + mo }
      st := { st with extraGow := st.extraGow + xg }
      st := { st with missingGow := st.missingGow + mg }
  return st

def runDistrib (φ : Cnf) (st0 : DiStat) : DiStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              st := { st with joins := st.joins + 1 }
              let J := join e hst
              -- the reader's review
              st := distribCheck s!"review key {d.step}:{d.index}" (filterAllAgg J []) (filterAllAgg e []) (filterAllAgg hst []) st
              -- every send the joined state will make
              for d' in mapSons φ d.step d.index do
                st := distribCheck s!"send key {d.step}:{d.index} -> {d'.step}:{d'.index}" (send J d') (send e d') (send hst d') st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportDi (name : String) (st : DiStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} checks={st.sends} bothDead={st.bothDead} oneAlive={st.oneAlive} bothAlive={st.bothAlive} VALIDITY_DIFFERS={st.VALIDITY_DIFFERS} equal={st.equal} DIFFER={st.DIFFER} | extraNodes={st.extraNodes} missingNodes={st.missingNodes} extraOwners={st.extraOwners} missingOwners={st.missingOwners} extraGow={st.extraGow} missingGow={st.missingGow} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Restriction (v138): is the review of a join, restricted to one side, a fixpoint of the review?
-- ============================================================

structure RsStat where
  checks : Nat := 0
  joinValid : Nat := 0
  idemFail : Nat := 0          -- reviewAgg R ≠ R (the review is not idempotent)
  sides : Nat := 0             -- non-empty restrictions examined
  restrValid : Nat := 0
  FIX_FAIL : Nat := 0          -- reviewAgg (R|a) removes something from R|a
  removedEntries : Nat := 0
  insideSide : Nat := 0        -- R|a ⊆ reviewAgg a (as measured before)
  NOT_INSIDE : Nat := 0
  covers : Nat := 0            -- R ⊆ join (review (R|a)) (review (R|b))
  COVER_FAIL : Nat := 0
  ex : List String := []

/-- `R` restricted to the nodes, links and entries `a` has. -/
def restrictTo (R a : GPathM) : GPathM := Id.run do
  let ta : Std.HashMap PathNodeId PNodeM := a.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let mut nodes : List PNodeM := []
  for n in R.nodes do
    match ta.get? n.id with
    | none => pure ()
    | some m =>
      let n1 : PNodeM := { n with owners := n.owners.filter m.owners.contains }
      let n2 : PNodeM := { n1 with parents := n.parents.filter m.parents.contains }
      let n3 : PNodeM := { n2 with sons := n.sons.filter m.sons.contains }
      nodes := nodes ++ [n3]
  -- links to nodes that are gone are dropped too
  let ids : Std.HashSet PathNodeId := Std.HashSet.ofList (nodes.map (·.id))
  nodes := nodes.map (fun n =>
    let n1 : PNodeM := { n with owners := n.owners.filter ids.contains }
    let n2 : PNodeM := { n1 with parents := n.parents.filter ids.contains }
    { n2 with sons := n.sons.filter ids.contains })
  let gow := R.gowners.filter (fun q => a.gowners.contains q && ids.contains q)
  return { R with nodes := nodes, gowners := gow }

/-- Entries of `a` that `b` lacks (nodes, owners, gowners): `b` is only a sub-state of `a` if 0. -/
def lacks (a b : GPathM) : Nat :=
  let (xn, _, xo, _, xg, _) := diffStates a b
  xn + xo + xg

def restrictCheck (tag : String) (a b : GPathM) (st0 : RsStat) : RsStat := Id.run do
  let mut st := { st0 with checks := st0.checks + 1 }
  let R := reviewAgg (join a b)
  if !isValid R then return st
  st := { st with joinValid := st.joinValid + 1 }
  if lacks R (reviewAgg R) + lacks (reviewAgg R) R != 0 then st := { st with idemFail := st.idemFail + 1 }
  -- the cover: every entry of R survives the review of some side's restriction
  let Fa := reviewAgg (restrictTo R a)
  let Fb := reviewAgg (restrictTo R b)
  let cov : Option GPathM :=
    if isValid Fa && isValid Fb then some (join Fa Fb) else if isValid Fa then some Fa
    else if isValid Fb then some Fb else none
  match cov with
  | none =>
    st := { st with COVER_FAIL := st.COVER_FAIL + 1 }
    if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"COVER FAIL {tag}: both reviewed restrictions invalid"] }
  | some C =>
    if lacks R C == 0 then st := { st with covers := st.covers + 1 }
    else
      st := { st with COVER_FAIL := st.COVER_FAIL + 1 }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"COVER FAIL {tag}: {lacks R C} entries of R outside"] }
  for (side, lbl) in [(a, "a"), (b, "b")] do
    let Rs := restrictTo R side
    if Rs.nodes.isEmpty then continue
    st := { st with sides := st.sides + 1 }
    if !isValid Rs then continue
    st := { st with restrValid := st.restrValid + 1 }
    let F := reviewAgg Rs
    let rem := lacks Rs F
    if rem != 0 then
      st := { st with FIX_FAIL := st.FIX_FAIL + 1 }
      st := { st with removedEntries := st.removedEntries + rem }
      if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"FIX FAIL {tag} side {lbl}: review removes {rem} entries of R|{lbl} (valid after: {isValid F})"] }
    let rS := reviewAgg side
    if isValid rS then
      if lacks Rs rS == 0 then st := { st with insideSide := st.insideSide + 1 }
      else
        st := { st with NOT_INSIDE := st.NOT_INSIDE + 1 }
        if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"NOT INSIDE {tag} side {lbl}: {lacks Rs rS} entries"] }
  return st

def runRestrict (φ : Cnf) (st0 : RsStat) : RsStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  let pinned (g : GPathM) (d : NodeId) : GPathM :=
    (reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              st := restrictCheck s!"review key {d.step}:{d.index}" e hst st
              for d' in mapSons φ d.step d.index do
                st := restrictCheck s!"send key {d.step}:{d.index} -> {d'.step}:{d'.index}" (pinned e d') (pinned hst d') st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportRs (name : String) (st : RsStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: checks={st.checks} joinValid={st.joinValid} idemFail={st.idemFail} sides={st.sides} restrValid={st.restrValid} FIX_FAIL={st.FIX_FAIL} removedEntries={st.removedEntries} insideSide={st.insideSide} NOT_INSIDE={st.NOT_INSIDE} covers={st.covers} COVER_FAIL={st.COVER_FAIL} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Split of supports (v139): split the review of a join by the side of the top-step witness,
-- and check every condition of `Sup` for each part inside its side
-- ============================================================

structure SpStat where
  joins : Nat := 0
  entries : Nat := 0
  UNCOVERED : Nat := 0         -- an entry with no top witness on either side
  bothTop : Nat := 0           -- a top node present in both sides
  fGow : Nat := 0
  fNode : Nat := 0
  fOwn : Nat := 0
  fCov : Nat := 0
  fPar : Nat := 0
  fSon : Nat := 0
  fAgg : Nat := 0
  fSym : Nat := 0
  fLink : Nat := 0
  inSide : Nat := 0
  UNANCHORED : Nat := 0
  domChecks : Nat := 0
  NOT_DOMINATED : Nat := 0     -- an anchored node's side entry that its anchor lacks        -- (x, v) in side S's tables but not anchored at a top of S
  ex : List String := []

def SpStat.bad (st : SpStat) (field : String) (msg : String) : SpStat :=
  let st := match field with
    | "gow" => { st with fGow := st.fGow + 1 } | "node" => { st with fNode := st.fNode + 1 }
    | "own" => { st with fOwn := st.fOwn + 1 } | "cov" => { st with fCov := st.fCov + 1 }
    | "par" => { st with fPar := st.fPar + 1 } | "son" => { st with fSon := st.fSon + 1 }
    | "agg" => { st with fAgg := st.fAgg + 1 } | "sym" => { st with fSym := st.fSym + 1 }
    | _ => { st with fLink := st.fLink + 1 }
  if st.ex.length < 10 then { st with ex := st.ex ++ [msg] } else st

/-- Check that the part of `R`'s relation anchored at `tops` is a support relation inside `g`. -/
def checkPart (lbl : String) (R g : GPathM) (rel : PathNodeId → PathNodeId → Bool)
    (tops : List PathNodeId) (st0 : SpStat) : SpStat := Id.run do
  let mut st := st0
  let cs := R.current_step
  let tg : Std.HashMap PathNodeId PNodeM := g.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let tR : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let part (x v : PathNodeId) : Bool := rel x v && tops.any (fun z => rel x z && rel v z)
  let members := R.nodes.map (·.id)
  let ownersOfR (x : PathNodeId) : List PathNodeId := match tR.get? x with | some m => m.owners.filter (fun w => tR.contains w) | none => []
  let inPart := members.filter (fun x => (ownersOfR x).any (fun v => part x v))
  let gow := Std.HashSet.ofList g.gowners
  for x in inPart do
    if !gow.contains x then st := st.bad "gow" s!"{lbl} gow {showPid x}"
    match tg.get? x with
    | none => st := st.bad "node" s!"{lbl} node {showPid x}"
    | some d =>
      let vs := (ownersOfR x).filter (fun v => part x v)
      -- cov
      for l in intRange 0 (cs - 1) do
        if !vs.any (fun v => v.id.step == l) then st := st.bad "cov" s!"{lbl} cov {showPid x} step {l}"
      for v in vs do
        if !d.owners.contains v then st := st.bad "own" s!"{lbl} own {showPid x} {showPid v}"
        if !part v x then st := st.bad "sym" s!"{lbl} sym {showPid x} {showPid v}"
        if x.parent_id.isSome then
          if !d.parents.any (fun c => part x c && part c x && part c v) then
            st := st.bad "par" s!"{lbl} par {showPid x} {showPid v}"
        if x.id.step != cs - 1 then
          let sons := g.nodes.filter (fun m => m.parents.contains x)
          if !sons.any (fun m => part x m.id && part m.id x && part m.id v) then
            st := st.bad "son" s!"{lbl} son {showPid x} {showPid v}"
        for l in intRange 0 (cs - 1) do
          if !(ownersOfR x).any (fun z => z.id.step == l && part x z && part v z) then
            st := st.bad "agg" s!"{lbl} agg {showPid x} {showPid v} step {l}"
        if v.id.step + 1 == x.id.step && part v x && !d.parents.contains v then
          st := st.bad "link" s!"{lbl} link {showPid x} {showPid v}"
  return st

def splitCheck (a b : GPathM) (st0 : SpStat) : SpStat := Id.run do
  let R := reviewAgg (join a b)
  if !isValid R then return st0
  let mut st := { st0 with joins := st0.joins + 1 }
  let cs := R.current_step
  let tR : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let ta : Std.HashMap PathNodeId PNodeM := a.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let tb : Std.HashMap PathNodeId PNodeM := b.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let relR (x v : PathNodeId) : Bool := match tR.get? x with | some m => m.owners.contains v && tR.contains v | none => false
  let relIn (t : Std.HashMap PathNodeId PNodeM) (x v : PathNodeId) : Bool :=
    relR x v && (match t.get? x with | some m => m.owners.contains v && t.contains v | none => false)
  let topShared := ((R.nodes.filter (fun m => m.id.id.step == cs - 1)).map (·.id)).any (fun z => ta.contains z && tb.contains z)
  if topShared then st := { st with bothTop := st.bothTop + 1 }
  -- the separation step: the highest step where no node of R is on both sides
  let mut sep : Int := cs - 1
  while sep ≥ 0 && ((R.nodes.filter (fun m => m.id.id.step == sep)).map (·.id)).any (fun z => ta.contains z && tb.contains z) do
    sep := sep - 1
  let top := (R.nodes.filter (fun m => m.id.id.step == sep)).map (·.id)
  let topsA := top.filter ta.contains
  let topsB := top.filter tb.contains
  let partA (x v : PathNodeId) : Bool := relIn ta x v && topsA.any (fun z => relIn ta x z && relIn ta v z)
  let partB (x v : PathNodeId) : Bool := relIn tb x v && topsB.any (fun z => relIn tb x z && relIn tb v z)
  for m in R.nodes do
    for v in m.owners do
      if !tR.contains v then continue
      st := { st with entries := st.entries + 1 }
      for (t, part, lbl) in [(ta, partA, "a"), (tb, partB, "b")] do
        if relIn t m.id v then
          st := { st with inSide := st.inSide + 1 }
          if !part m.id v then
            st := { st with UNANCHORED := st.UNANCHORED + 1 }
            if st.ex.length < 10 then st := { st with ex := st.ex ++ [s!"UNANCHORED side {lbl} {showPid m.id} {showPid v}"] }
      if !(partA m.id v || partB m.id v) then
        st := { st with UNCOVERED := st.UNCOVERED + 1 }
        if st.ex.length < 10 then st := { st with ex := st.ex ++ [s!"UNCOVERED {showPid m.id} {showPid v} inA={relIn ta m.id v} inB={relIn tb m.id v}"] }
  -- anchor dominance: an anchored node's side entries are its anchor's
  for (t, tops) in [(ta, topsA), (tb, topsB)] do
    for z in tops do
      for m in R.nodes do
        let x := m.id
        if !(relIn t x z) then continue
        for w in m.owners do
          if !(relIn t x w) then continue
          st := { st with domChecks := st.domChecks + 1 }
          if !(relIn t z w) then
            st := { st with NOT_DOMINATED := st.NOT_DOMINATED + 1 }
            if st.ex.length < 10 then st := { st with ex := st.ex ++ [s!"NOT DOMINATED anchor {showPid z} node {showPid x} entry {showPid w}"] }
  st := checkPart "a" R a (relIn ta) topsA st
  st := checkPart "b" R b (relIn tb) topsB st
  return st

def runSplit (φ : Cnf) (st0 : SpStat) : SpStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  let pinned (g : GPathM) (d : NodeId) : GPathM :=
    (reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              st := splitCheck e hst st
              for d' in mapSons φ d.step d.index do
                st := splitCheck (pinned e d') (pinned hst d') st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportSp (name : String) (st : SpStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} entries={st.entries} UNCOVERED={st.UNCOVERED} bothTop={st.bothTop} inSide={st.inSide} UNANCHORED={st.UNANCHORED} domChecks={st.domChecks} NOT_DOMINATED={st.NOT_DOMINATED} | fails gow={st.fGow} node={st.fNode} own={st.fOwn} cov={st.fCov} par={st.fPar} son={st.fSon} agg={st.fAgg} sym={st.fSym} link={st.fLink} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Pieces (v139): the joins `split_branch` performs — merging the runs of single-key pieces —
-- checked against the distributive equations and the support split
-- ============================================================

structure PcStat where
  splits : Nat := 0
  merges : Nat := 0
  sharedTop : Nat := 0
  di : DiStat := {}
  sp : SpStat := {}
  capped : Nat := 0

def runPieces (φ : Cnf) (maxK : Nat) (cap : Nat) (st0 : PcStat) : PcStat := Id.run do
  let mut st := st0
  let lines := aggLines φ
  let n := lines.length
  let pinnedF (g : GPathM) (d : NodeId) : GPathM :=
    (reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for k in [0:min n maxK] do
    let Lk := lines[k]!
    if Lk.length < 2 then continue
    if Lk.length > cap then
      st := { st with capped := st.capped + 1 }
      continue
    st := { st with splits := st.splits + 1 }
    let mut pieces : List PureLine := Lk.map (fun x => [x])
    for _ in [k:n - 1] do
      -- merge the pieces' current lines, checking every join the merge performs
      let mut acc : PureLine := []
      for P in pieces do
        for kv in P do
          match acc.find? (fun x => x.1 == kv.1) with
          | some (_, e) =>
            if okJoin e kv.2 then
              st := { st with merges := st.merges + 1 }
              let cs := e.current_step
              let topE := (e.nodes.filter (fun m => m.id.id.step == cs - 1)).map (·.id)
              if topE.any (fun z => (kv.2.node? z).isSome) then st := { st with sharedTop := st.sharedTop + 1 }
              let J := join e kv.2
              let mut di := st.di
              di := distribCheck s!"piece review {kv.1.step}:{kv.1.index}" (filterAllAgg J []) (filterAllAgg e []) (filterAllAgg kv.2 []) di
              let mut sp := st.sp
              sp := splitCheck e kv.2 sp
              for d in mapSons φ kv.1.step kv.1.index do
                di := distribCheck s!"piece send {kv.1.step}:{kv.1.index} -> {d.step}:{d.index}" (send J d) (send e d) (send kv.2 d) di
                sp := splitCheck (pinnedF e d) (pinnedF kv.2 d) sp
              st := { st with di := di, sp := sp }
          | none => pure ()
          acc := insertPure acc kv.1 kv.2
      pieces := pieces.map (fun P => advanceLine φ P)
  return st

def reportPc (name : String) (st : PcStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: splits={st.splits} merges={st.merges} sharedTop={st.sharedTop} capped={st.capped} | {ms}ms"
  reportDi "  distrib" st.di 0
  reportSp "  split" st.sp 0

-- ============================================================
-- The oracle inside the machine (v138): is each machine state the join of the valid single-path
-- states with its key, and does the send distribute over that join?
-- ============================================================

structure OStat where
  lines : Nat := 0
  states : Nat := 0
  paths : Nat := 0
  NO_PATH : Nat := 0          -- a valid machine state with no valid single path at its key
  equal : Nat := 0            -- machine state = join of the single-path states (as sets)
  machineExtra : Nat := 0     -- machine state has entries the join lacks
  joinExtra : Nat := 0        -- the join has entries the machine lacks
  sends : Nat := 0
  sendEqual : Nat := 0
  SEND_EXCEEDS : Nat := 0     -- send(U) not contained in join of valid send(B)
  SEND_ALIVE_ALL_DEAD : Nat := 0
  capped : Nat := 0
  ex : List String := []

def joinAll (bs : List GPathM) : Option GPathM :=
  match bs with
  | [] => none
  | b :: rest => some (rest.foldl join b)

def runOracle (φ : Cnf) (cap : Nat) (st0 : OStat) : OStat := Id.run do
  let mut st := st0
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  let mut line := pureInit φ
  let mut singles : List (NodeId × GPathM) := pureInit φ
  for _ in [0:(stepCount φ).toNat] do
    if singles.length > cap then
      st := { st with capped := st.capped + 1 }
      return st
    st := { st with lines := st.lines + 1, paths := st.paths + singles.length }
    -- compare each machine state with the join of its key's single-path states
    for kv in line do
      if !isValid kv.2 then continue
      st := { st with states := st.states + 1 }
      let bs := (singles.filter (fun x => x.1 == kv.1)).map (·.2)
      match joinAll bs with
      | none =>
        st := { st with NO_PATH := st.NO_PATH + 1 }
        if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"NO PATH key {kv.1.step}:{kv.1.index}"] }
      | some U =>
        let (xn, mn, xo, mo, xg, mg) := diffStates kv.2 U
        if xn + mn + xo + mo + xg + mg == 0 then st := { st with equal := st.equal + 1 }
        st := { st with machineExtra := st.machineExtra + xn + xo + xg, joinExtra := st.joinExtra + mn + mo + mg }
        -- the send from U against the join of the single-path sends
        for d in mapSons φ kv.1.step kv.1.index do
          st := { st with sends := st.sends + 1 }
          let sU := send U d
          let alive := (bs.map (fun b => send b d)).filter isValid
          if isValid sU then
            match joinAll alive with
            | none =>
              st := { st with SEND_ALIVE_ALL_DEAD := st.SEND_ALIVE_ALL_DEAD + 1 }
              if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"SEND ALIVE, ALL PATHS DEAD key {kv.1.step}:{kv.1.index} -> {d.step}:{d.index}"] }
            | some R =>
              let (xn', mn', xo', mo', xg', mg') := diffStates sU R
              if xn' + xo' + xg' == 0 then
                if mn' + mo' + mg' == 0 then st := { st with sendEqual := st.sendEqual + 1 }
              else
                st := { st with SEND_EXCEEDS := st.SEND_EXCEEDS + 1 }
                if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"SEND EXCEEDS key {kv.1.step}:{kv.1.index} -> {d.step}:{d.index}: nodes={xn'} owners={xo'} gow={xg'}"] }
    -- advance both
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then next := insertPure next d hst
    line := next
    let mut ns : List (NodeId × GPathM) := []
    for kv in singles do
      for d in mapSons φ kv.1.step kv.1.index do
        let b := send kv.2 d
        if isValid b then ns := (d, b) :: ns
    singles := ns.reverse
  return st

def reportO (name : String) (st : OStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: lines={st.lines} states={st.states} singlePaths={st.paths} NO_PATH={st.NO_PATH} equal={st.equal} machineExtra={st.machineExtra} joinExtra={st.joinExtra} | sends={st.sends} sendEqual={st.sendEqual} SEND_EXCEEDS={st.SEND_EXCEEDS} SEND_ALIVE_ALL_DEAD={st.SEND_ALIVE_ALL_DEAD} capped={st.capped} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Path unions (v139): the review of a union of single paths, after unary pins, against the union
-- of the paths that pass the pins — on random unions, not only the machine's
-- ============================================================

structure PuStat where
  trials : Nat := 0
  unionValid : Nat := 0
  equal : Nat := 0
  EXTRA : Nat := 0             -- the reviewed union keeps entries no passing path has
  MISSING : Nat := 0           -- a passing path lost
  noneAlive : Nat := 0
  ALIVE_NO_PATH : Nat := 0     -- the reviewed union is valid but no path passes
  ex : List String := []

/-- The single-path state of a map path. -/
def pathState (p : List NodeId) : GPathM :=
  match p with
  | [] => GPathM.empty
  | d :: rest => rest.foldl (fun g d' => addNode g d' "") (GPathM.initSeed d "")

/-- Close a set of map paths under recombination at shared map nodes: a prefix ending at a map node and
a suffix leaving it make a path. -/
def recombine (ps : List (List NodeId)) : List (List NodeId) := Id.run do
  let mut cur := ps.eraseDups
  let mut changed := true
  while changed do
    changed := false
    let mut add : List (List NodeId) := []
    for p in cur do
      for q in cur do
        for i in [0:p.length] do
          if p[i]? == q[i]? then
            let r := p.take (i + 1) ++ q.drop (i + 1)
            if !cur.contains r && !add.contains r then add := add ++ [r]
    if !add.isEmpty then
      cur := cur ++ add
      changed := true
  return cur

/-- All map paths (last step fixed at index 0) satisfying random requirements
"(t, y) ⇒ (i, r)", with `nreq` requirements. -/
def csPaths (steps width nreq : Nat) (rng0 : AbsSat.SatMachine.DiffTest.Rng) :
    List (List NodeId) × AbsSat.SatMachine.DiffTest.Rng := Id.run do
  let mut rng := rng0
  let mut reqs : List (NodeId × NodeId) := []
  for _ in [0:nreq] do
    let (r1, t) := rng.below (steps - 2)
    let (r2, y) := r1.below width
    let (r3, i) := r2.below (t + 1)
    let (r4, r) := r3.below width
    rng := r4
    reqs := reqs ++ [(⟨((t + 1 : Nat) : Int), (y : Int)⟩, ⟨(i : Int), (r : Int)⟩)]
  -- enumerate
  let mut all : List (List NodeId) := [[]]
  for sIdx in [0:steps] do
    let choices : List Nat := if sIdx + 1 == steps then [0] else List.range width
    all := all.flatMap (fun p => choices.map (fun i => p ++ [⟨(sIdx : Int), (i : Int)⟩]))
  let ok (p : List NodeId) : Bool :=
    reqs.all (fun (a, b) => !(p.contains a) || p.contains b)
  return (all.filter ok, rng)

def runPathCsp (steps width nreq trials seed : Nat) : PuStat := Id.run do
  let mut st : PuStat := {}
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  for _ in [0:trials] do
    let (ps, r0) := csPaths steps width nreq rng
    rng := r0
    if ps.isEmpty then continue
    let (r2, npins) := rng.below 3
    rng := r2
    let mut pins : List NodeId := []
    for _ in [0:npins + 1] do
      let (r3, s) := rng.below (steps - 1)
      let (r4, i) := r3.below width
      rng := r4
      pins := pins ++ [⟨(s : Int), (i : Int)⟩]
    let passes (p : List NodeId) : Bool := pins.all (fun r => p.all (fun n => n.step != r.step || n == r))
    let states := ps.map pathState
    let U := match states with | [] => GPathM.empty | g :: rest => rest.foldl join g
    let R := filterAllAgg U pins
    st := { st with trials := st.trials + 1 }
    let alive := (ps.filter passes).map pathState
    if !isValid R then continue
    st := { st with unionValid := st.unionValid + 1 }
    match alive with
    | [] =>
      st := { st with ALIVE_NO_PATH := st.ALIVE_NO_PATH + 1 }
    | g :: rest =>
      let A := rest.foldl join g
      let (xn, mn, xo, mo, xg, mg) := diffStates R A
      if xn + xo + xg == 0 && mn + mo + mg == 0 then st := { st with equal := st.equal + 1 }
      if xn + xo + xg != 0 then
        st := { st with EXTRA := st.EXTRA + 1 }
        if st.ex.length < 4 then st := { st with ex := st.ex ++ [s!"EXTRA owners={xo} paths={ps.length} pins={pins.map (fun r => (r.step, r.index))}"] }
      if mn + mo + mg != 0 then st := { st with MISSING := st.MISSING + 1 }
  return st

def runPathUnion (steps width paths trials seed : Nat) (closed : Bool := false) : PuStat := Id.run do
  let mut st : PuStat := {}
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  for _ in [0:trials] do
    -- random map paths ending at the same final map node
    let mut ps : List (List NodeId) := []
    for _ in [0:paths] do
      let mut p : List NodeId := []
      for s in [0:steps] do
        if s + 1 == steps then p := p ++ [⟨(s : Int), 0⟩]
        else
          let (r1, i) := rng.below width
          rng := r1
          p := p ++ [⟨(s : Int), (i : Int)⟩]
      ps := ps ++ [p]
    ps := if closed then recombine ps else ps.eraseDups
    -- random unary pins below the top
    let (r2, npins) := rng.below 3
    rng := r2
    let mut pins : List NodeId := []
    for _ in [0:npins + 1] do
      let (r3, s) := rng.below (steps - 1)
      let (r4, i) := r3.below width
      rng := r4
      pins := pins ++ [⟨(s : Int), (i : Int)⟩]
    let passes (p : List NodeId) : Bool := pins.all (fun r => p.all (fun n => n.step != r.step || n == r))
    let states := ps.map pathState
    let U := match states with | [] => GPathM.empty | g :: rest => rest.foldl join g
    let R := filterAllAgg U pins
    st := { st with trials := st.trials + 1 }
    let alive := (ps.filter passes).map pathState
    if !isValid R then
      continue
    st := { st with unionValid := st.unionValid + 1 }
    match alive with
    | [] =>
      st := { st with ALIVE_NO_PATH := st.ALIVE_NO_PATH + 1 }
      if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"ALIVE NO PATH paths={ps.map (fun p => p.map (·.index))} pins={pins.map (fun r => (r.step, r.index))}"] }
    | g :: rest =>
      let A := rest.foldl join g
      let (xn, mn, xo, mo, xg, mg) := diffStates R A
      if xn + xo + xg == 0 && mn + mo + mg == 0 then st := { st with equal := st.equal + 1 }
      if xn + xo + xg != 0 then
        st := { st with EXTRA := st.EXTRA + 1 }
        if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"EXTRA nodes={xn} owners={xo} gow={xg} paths={ps.map (fun p => p.map (·.index))} pins={pins.map (fun r => (r.step, r.index))}"] }
      if mn + mo + mg != 0 then st := { st with MISSING := st.MISSING + 1 }
  return st

def reportPu (name : String) (st : PuStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: trials={st.trials} unionValid={st.unionValid} equal={st.equal} EXTRA={st.EXTRA} MISSING={st.MISSING} ALIVE_NO_PATH={st.ALIVE_NO_PATH} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Linked chains (v139): in a reviewed state, is every parent-linked chain of surviving nodes pairwise
-- owned?
-- ============================================================

structure LkStat where
  states : Nat := 0
  chains : Nat := 0
  owned : Nat := 0
  NOT_OWNED : Nat := 0
  truncated : Nat := 0
  ex : List String := []

partial def linkedWalk (g : GPathM) (tbl : Std.HashMap PathNodeId PNodeM) (gow : Std.HashSet PathNodeId)
    (chain : List PathNodeId) (st0 : LkStat) (budget : Nat) : LkStat × Nat := Id.run do
  let mut st := st0
  let x := chain.head!
  if x.id.step == 0 then
    st := { st with chains := st.chains + 1 }
    let ok := chain.all (fun p => chain.all (fun q => p == q ||
      (match tbl.get? p with | some m => m.owners.contains q | none => false)))
    if ok then st := { st with owned := st.owned + 1 }
    else
      st := { st with NOT_OWNED := st.NOT_OWNED + 1 }
      if st.ex.length < 4 then st := { st with ex := st.ex ++ [s!"LINKED NOT OWNED {chain.map showPid}"] }
    return (st, budget)
  let parents := match tbl.get? x with | some m => m.parents.filter (fun p => gow.contains p && tbl.contains p) | none => []
  let mut bud := budget
  for p in parents do
    if bud == 0 then return ({ st with truncated := st.truncated + 1 }, 0)
    bud := bud - 1
    let (st', b') := linkedWalk g tbl gow (p :: chain) st bud
    st := st'
    bud := b'
  return (st, bud)

def runLinked (φ : Cnf) (budget : Nat) (st0 : LkStat) : LkStat := Id.run do
  let mut st := st0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      st := { st with states := st.states + 1 }
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (st', b') := linkedWalk G tbl gow [n.id] st bud
        st := st'
        bud := b'
  return st

def reportLk (name : String) (st : LkStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} linkedChains={st.chains} owned={st.owned} NOT_OWNED={st.NOT_OWNED} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Helly-3 on exact states (v139): pairwise co-realizable entry (x, v) and pinned map node m at step s
-- (some z with id m owning both) ⟹ a solution chain through x, v and a node of map m at step s?
-- ============================================================

structure H3Stat where
  states : Nat := 0
  chains : Nat := 0
  checks : Nat := 0
  HELLY3_FAIL : Nat := 0
  truncated : Nat := 0
  ex : List String := []

partial def solWalk (tbl : Std.HashMap PathNodeId PNodeM) (gow : Std.HashSet PathNodeId)
    (chain : List PathNodeId) (acc : Array (List PathNodeId)) (budget : Nat) : Array (List PathNodeId) × Nat := Id.run do
  let x := chain.head!
  -- keep only pairwise-owned partial chains
  if x.id.step == 0 then return (acc.push chain, budget)
  let parents := match tbl.get? x with | some m => m.parents.filter (fun p => gow.contains p && tbl.contains p) | none => []
  let mut acc := acc
  let mut bud := budget
  for p in parents do
    let pm := tbl.get! p
    if !chain.all (fun q => pm.owners.contains q && (match tbl.get? q with | some qm => qm.owners.contains p | none => false)) then continue
    if bud == 0 then return (acc, 0)
    bud := bud - 1
    let (a', b') := solWalk tbl gow (p :: chain) acc bud
    acc := a'
    bud := b'
  return (acc, bud)

def runHelly3 (φ : Cnf) (budget : Nat) (st0 : H3Stat) : H3Stat := Id.run do
  let mut st := st0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      st := { st with states := st.states + 1 }
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut sols : Array (List PathNodeId) := #[]
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (a', b') := solWalk tbl gow [n.id] sols bud
        sols := a'
        bud := b'
      if bud == 0 then
        st := { st with truncated := st.truncated + 1 }
        continue
      st := { st with chains := st.chains + sols.size }
      -- for each solution: its node ids indexed by step
      let solArr := sols.map (fun c => c.toArray)
      -- chains through each node
      let mut through : Std.HashMap PathNodeId (List Nat) := {}
      for i in [0:solArr.size] do
        for p in solArr[i]! do
          through := through.insert p (i :: through.getD p [])
      for m in G.nodes do
        let x := m.id
        for v in m.owners do
          if v == x || !tbl.contains v then continue
          let cx := through.getD x []
          let cxv := cx.filter (fun i => solArr[i]!.contains v)
          for sIdx in [0:cs.toNat] do
            let sI : Int := sIdx
            if sI == x.id.step || sI == v.id.step then continue
            -- map ids at step s owned by both x and v through some node
            let zs := (m.owners.filter (fun z => z.id.step == sI)).filter (fun z =>
              match tbl.get? v with | some vm => vm.owners.contains z | none => false)
            let maps := (zs.map (·.id)).eraseDups
            for mid in maps do
              st := { st with checks := st.checks + 1 }
              let ok := cxv.any (fun i => solArr[i]!.any (fun p => p.id == mid))
              if !ok then
                st := { st with HELLY3_FAIL := st.HELLY3_FAIL + 1 }
                if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"HELLY3 FAIL x={showPid x} v={showPid v} map={mid.step}.{mid.index}"] }
  return st

def reportH3 (name : String) (st : H3Stat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} solutionChains={st.chains} checks={st.checks} HELLY3_FAIL={st.HELLY3_FAIL} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- FilterSound for arbitrary single pins on the machine's exact states (v139)
-- ============================================================

structure PeStat where
  states : Nat := 0
  pins : Nat := 0
  pinValid : Nat := 0
  exact : Nat := 0
  EXTRA : Nat := 0
  VALID_NO_SOL : Nat := 0
  MISSING : Nat := 0
  truncated : Nat := 0
  ex : List String := []

def runPinExact (φ : Cnf) (budget : Nat) (st0 : PeStat) : PeStat := Id.run do
  let mut st := st0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      st := { st with states := st.states + 1 }
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut sols : Array (List PathNodeId) := #[]
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (a', b') := solWalk tbl gow [n.id] sols bud
        sols := a'
        bud := b'
      if bud == 0 then
        st := { st with truncated := st.truncated + 1 }
        continue
      let maps := (G.gowners.map (·.id)).eraseDups
      for m in maps do
        if m.step == cs - 1 then continue
        st := { st with pins := st.pins + 1 }
        let R := filterAllAgg G [m]
        let through := sols.toList.filter (fun c => c.any (fun p => p.id == m))
        if !isValid R then
          if !through.isEmpty then
            st := { st with MISSING := st.MISSING + 1 }
          continue
        st := { st with pinValid := st.pinValid + 1 }
        match through.map (fun c => pathState (c.map (·.id))) with
        | [] =>
          st := { st with VALID_NO_SOL := st.VALID_NO_SOL + 1 }
          if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"VALID, NO SOLUTION through pin {m.step}.{m.index} (state key {kv.1.step}.{kv.1.index})"] }
        | g :: rest =>
          let A := rest.foldl join g
          let (xn, mn, xo, mo, xg, mg) := diffStates R A
          if xn + xo + xg == 0 && mn + mo + mg == 0 then st := { st with exact := st.exact + 1 }
          if xn + xo + xg != 0 then
            st := { st with EXTRA := st.EXTRA + 1 }
            if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"EXTRA after pin {m.step}.{m.index}: nodes={xn} owners={xo} gow={xg} (state key {kv.1.step}.{kv.1.index})"] }
          if mn + mo + mg != 0 then st := { st with MISSING := st.MISSING + 1 }
  return st

/-- Subsets of `l` with at least two elements and missing at least one (capped). -/
def weakSubsets (l : List NodeId) (cap : Nat) : List (List NodeId) :=
  let n := l.length
  if n < 3 then [] else
  ((List.range (2 ^ n)).filterMap fun mask =>
    let sub := (l.zipIdx).filterMap fun (x, i) => if (mask >>> i) % 2 == 1 then some x else none
    if sub.length ≥ 2 && sub.length < n then some sub else none).take cap

/-- v144: one weak requirement (a set of allowed map nodes at a step) on an exact reader's state, then
the review: is the result exactly the union of the surviving paths? -/
def runWeakExact (φ : Cnf) (budget : Nat) (cap : Nat) (st0 : PeStat) : PeStat := Id.run do
  let mut st := st0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      st := { st with states := st.states + 1 }
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut sols : Array (List PathNodeId) := #[]
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (a', b') := solWalk tbl gow [n.id] sols bud
        sols := a'
        bud := b'
      if bud == 0 then
        st := { st with truncated := st.truncated + 1 }
        continue
      let maps := (G.gowners.map (·.id)).eraseDups
      for s in ((List.range (cs - 1).toNat).map (fun (i : Nat) => (i : Int)) : List Int) do
        let here := maps.filter (·.step == s)
        for sub in weakSubsets here cap do
          st := { st with pins := st.pins + 1 }
          let R := filterAllAgg (filterWeak G (s, sub)) []
          let through := sols.toList.filter (fun c => c.any (fun p => p.id.step == s && sub.contains p.id))
          if !isValid R then
            if !through.isEmpty then st := { st with MISSING := st.MISSING + 1 }
            continue
          st := { st with pinValid := st.pinValid + 1 }
          match through.map (fun c => pathState (c.map (·.id))) with
          | [] =>
            st := { st with VALID_NO_SOL := st.VALID_NO_SOL + 1 }
          | g :: rest =>
            let A := rest.foldl join g
            let (xn, mn, xo, mo, xg, mg) := diffStates R A
            if xn + xo + xg == 0 && mn + mo + mg == 0 then st := { st with exact := st.exact + 1 }
            if xn + xo + xg != 0 then
              st := { st with EXTRA := st.EXTRA + 1 }
              if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"EXTRA after weak step {s} set size {sub.length}: nodes={xn} owners={xo} gow={xg}"] }
            if mn + mo + mg != 0 then st := { st with MISSING := st.MISSING + 1 }
  return st

def reportPe (name : String) (st : PeStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} pins={st.pins} pinValid={st.pinValid} exact={st.exact} EXTRA={st.EXTRA} VALID_NO_SOL={st.VALID_NO_SOL} MISSING={st.MISSING} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Why (v139): on a Helly-3 failure (x, v, map m), pin m and see how the review drops (x, v)
-- ============================================================

/-- Is `y` connected to a node with map id `m` at step `s` by parent links (downward) or son links
(upward), inside `g`? -/
partial def linkedTo (tbl : Std.HashMap PathNodeId PNodeM) (m : NodeId) (up : Bool) (y : PathNodeId) : Bool :=
  if y.id.step == m.step then y.id == m
  else match tbl.get? y with
    | none => false
    | some n =>
      if up then n.sons.any (fun c => c.id.step ≤ m.step && linkedTo tbl m up c)
      else n.parents.any (fun c => c.id.step ≥ m.step && linkedTo tbl m up c)

def runWhy (φ : Cnf) (budget : Nat) (maxEx : Nat) : IO Unit := do
  let mut shown := 0
  let mut tally : Std.HashMap String Nat := {}
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut sols : Array (List PathNodeId) := #[]
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (a', b') := solWalk tbl gow [n.id] sols bud
        sols := a'
        bud := b'
      let solArr := sols.map (fun c => c.toArray)
      for m in G.nodes do
        let x := m.id
        for v in m.owners do
          if v == x || !tbl.contains v then continue
          for sIdx in [0:cs.toNat] do
            let sI : Int := sIdx
            if sI == x.id.step || sI == v.id.step then continue
            let zs := (m.owners.filter (fun z => z.id.step == sI)).filter (fun z =>
              match tbl.get? v with | some vm => vm.owners.contains z | none => false)
            for mid in (zs.map (·.id)).eraseDups do
              let ok := solArr.any (fun c => c.contains x && c.contains v && c.any (fun p => p.id == mid))
              if ok then continue
              if tally.fold (fun acc _ n => acc + n) 0 ≥ 300 then continue
              -- a Helly-3 failure: pin mid and look
              let R := filterAllAgg G [mid]
              let tR : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc n => acc.insert n.id n) {}
              let xIn := tR.contains x
              let vIn := tR.contains v
              let pairIn := match tR.get? x with | some n => n.owners.contains v | none => false
              -- where x and v stand relative to the pinned step
              let rel (y : PathNodeId) : String :=
                if y.id.step < sI then "below" else "above"
              let key := s!"x {rel x} v {rel v} | x survives {xIn} v survives {vIn} pair {pairIn}"
              tally := tally.insert key (tally.getD key 0 + 1)
              if shown < maxEx then
                shown := shown + 1
                let xl := linkedTo tbl mid (x.id.step < sI) x
                let vl := linkedTo tbl mid (v.id.step < sI) v
                IO.println s!"  x={showPid x} v={showPid v} pin={mid.step}.{mid.index} | {key} | x linked to pin {xl}, v linked to pin {vl}"
  for (k, n) in tally.toList do IO.println s!"  TALLY {n}  {k}"

-- ============================================================
-- Slice closed under links (v139): in an exact state, is every linked chain whose nodes all own a common
-- v (and passes v) pairwise owned?
-- ============================================================

structure ScStat where
  states : Nat := 0
  chains : Nat := 0
  owned : Nat := 0
  NOT_OWNED : Nat := 0
  truncated : Nat := 0
  ex : List String := []

partial def sliceWalk (tbl : Std.HashMap PathNodeId PNodeM) (gow : Std.HashSet PathNodeId) (v : PathNodeId)
    (chain : List PathNodeId) (st0 : ScStat) (budget : Nat) : ScStat × Nat := Id.run do
  let mut st := st0
  let x := chain.head!
  if x.id.step == 0 then
    if !chain.contains v then return (st, budget)
    st := { st with chains := st.chains + 1 }
    let ok := chain.all (fun p => chain.all (fun q => p == q ||
      (match tbl.get? p with | some m => m.owners.contains q | none => false)))
    if ok then st := { st with owned := st.owned + 1 }
    else
      st := { st with NOT_OWNED := st.NOT_OWNED + 1 }
      if st.ex.length < 4 then st := { st with ex := st.ex ++ [s!"v={showPid v} chain {chain.map showPid}"] }
    return (st, budget)
  let parents := match tbl.get? x with
    | some m => m.parents.filter (fun p => gow.contains p &&
        (match tbl.get? p with | some pm => pm.owners.contains v | none => false))
    | none => []
  let mut bud := budget
  for p in parents do
    if bud == 0 then return ({ st with truncated := st.truncated + 1 }, 0)
    bud := bud - 1
    let (st', b') := sliceWalk tbl gow v (p :: chain) st bud
    st := st'
    bud := b'
  return (st, bud)

def runSliceClosed (φ : Cnf) (budget : Nat) (st0 : ScStat) : ScStat := Id.run do
  let mut st := st0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      st := { st with states := st.states + 1 }
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut bud := budget
      for vn in G.nodes do
        let v := vn.id
        for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
          if !gow.contains n.id || !n.owners.contains v then continue
          let (st', b') := sliceWalk tbl gow v [n.id] st bud
          st := st'
          bud := b'
  return st

def reportSc (name : String) (st : ScStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} linkedChainsInSlices={st.chains} owned={st.owned} NOT_OWNED={st.NOT_OWNED} truncated={st.truncated} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Ghosts (v140): after a pin on an exact state, which operation of the review, in which round, removes
-- each entry that no surviving solution holds (a "ghost"), and at what distance from the pinned step?
-- ============================================================

def hasEntry (g : GPathM) (x v : PathNodeId) : Bool :=
  match g.node? x with | some n => n.owners.contains v | none => false

def runGhosts (φ : Cnf) (budget : Nat) : IO Unit := do
  let mut tally : Std.HashMap String Nat := {}
  let mut ghostsTotal := 0
  let mut nodeDeaths := 0
  let mut survivors := 0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut sols : Array (List PathNodeId) := #[]
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (a', b') := solWalk tbl gow [n.id] sols bud
        sols := a'
        bud := b'
      if bud == 0 then continue
      let maps := (G.gowners.map (·.id)).eraseDups
      for m in maps do
        if m.step == cs - 1 then continue
        let through := sols.toList.filter (fun c => c.any (fun p => p.id == m))
        -- ghosts: entries of G no solution through the pin holds
        let mut ghosts : List (PathNodeId × PathNodeId) := []
        for n in G.nodes do
          for v in n.owners do
            if v == n.id || !tbl.contains v then continue
            if !(through.any (fun c => c.contains n.id && c.contains v)) then
              ghosts := (n.id, v) :: ghosts
        if ghosts.isEmpty then continue
        ghostsTotal := ghostsTotal + ghosts.length
        -- the review, step by step
        let mut g := [m].foldl filterRequire G
        let mut alive := ghosts.filter (fun (x, v) => hasEntry g x v)
        -- entries already gone with the pin (the node lost as a global owner does not remove entries)
        let mut round := 0
        let mut fuel := 200
        let mut done := false
        while !done && fuel > 0 do
          fuel := fuel - 1
          round := round + 1
          -- base review to its fixpoint
          let mut inner := 0
          let mut innerDone := false
          while !innerDone && inner < 200 do
            inner := inner + 1
            if !isValid g then
              innerDone := true
              continue
            let m0 := GPathM.measure g
            let ops : List (String × (GPathM → GPathM)) :=
              [("clean", cleanInvalid), ("parents", reviewParents), ("sons", reviewSons)]
            for (lbl, op) in ops do
              let g' := op g
              -- ghost nodes: live nodes of g' on no surviving solution
              if inner == 1 && round == 1 then
                let mut gn := 0
                let mut live := 0
                for n in g'.nodes do
                  live := live + 1
                  if !(through.any (fun c => c.contains n.id)) then gn := gn + 1
                let key := s!"  NODES after pass-1 {lbl}: ghost nodes"
                tally := tally.insert key (tally.getD key 0 + gn)
                let key2 := s!"  NODES after pass-1 {lbl}: live nodes"
                tally := tally.insert key2 (tally.getD key2 0 + live)
              -- survivors by direction, after this operation of the first pass
              if inner == 1 && round == 1 then
                for (x, v) in alive do
                  if !hasEntry g' x v then continue
                  let xs := x.id.step
                  let vs := v.id.step
                  let cls :=
                    if xs == m.step then "x at the pin"
                    else if xs > m.step then (if vs < xs then "A: x above pin, v below x" else "B: x above pin, v above x")
                    else (if vs > xs then "C: x below pin, v above x" else "D: x below pin, v below x")
                  let key := s!"  after pass-1 {lbl}: {cls}"
                  tally := tally.insert key (tally.getD key 0 + 1)
              let (gone, keep) := alive.partition (fun (x, v) => !hasEntry g' x v)
              for (x, v) in gone do
                let nodeGone := (g'.node? x).isNone
                if nodeGone then nodeDeaths := nodeDeaths + 1
                let _dist := min (Int.natAbs (x.id.step - m.step)) (Int.natAbs (v.id.step - m.step))
                let key := s!"pass {inner} {lbl}{if nodeGone then " (node removed)" else ""}"
                tally := tally.insert key (tally.getD key 0 + 1)
              alive := keep
              g := g'
            if GPathM.measure g ≥ m0 then innerDone := true
          if !isValid g then
            done := true
            continue
          let before := GPathM.measure g
          -- before the sweep: is every surviving ghost directly detectable as a pair?
          if round == 1 then
            for (x, v) in alive do
              let key := match g.node? x, g.node? v with
                | some nx, some nv =>
                  if !nv.owners.contains x then
                    let dx := Int.natAbs (x.id.step - m.step)
                    let dv := Int.natAbs (v.id.step - m.step)
                    let side := if (x.id.step - m.step) * (v.id.step - m.step) > 0 then "same side" else "opposite sides"
                    if dv < dx then s!"  pre-sweep ghost: ASYMMETRIC, the one that dropped is NEARER the pin ({side})"
                    else if dv > dx then s!"  pre-sweep ghost: ASYMMETRIC, the one that dropped is FARTHER from the pin ({side})"
                    else s!"  pre-sweep ghost: ASYMMETRIC, equally near ({side})"
                  else if !sharesEveryStep g.current_step nx.owners nv.owners then "  pre-sweep ghost: a step with NO COMMON OWNER"
                  else "  pre-sweep ghost: NOT DIRECTLY DETECTABLE"
                | _, _ => "  pre-sweep ghost: node missing"
              tally := tally.insert key (tally.getD key 0 + 1)
          let g' := aggSweep g
          let (gone, keep) := alive.partition (fun (x, v) => !hasEntry g' x v)
          for (x, v) in gone do
            let nodeGone := (g'.node? x).isNone
            if nodeGone then nodeDeaths := nodeDeaths + 1
            let dist := min (Int.natAbs (x.id.step - m.step)) (Int.natAbs (v.id.step - m.step))
            let key := s!"round {round} aggressive after {inner} passes dist {min dist 6}"
            tally := tally.insert key (tally.getD key 0 + 1)
          alive := keep
          if GPathM.measure g' < before then g := g' else done := true
        survivors := survivors + alive.length
  IO.println s!"ghosts={ghostsTotal} survivors={survivors} nodeRemovals={nodeDeaths}"
  let rows := tally.toList.toArray.qsort (fun a b => a.1 < b.1)
  for (k, n) in rows do IO.println s!"  {n}  {k}"

-- ============================================================
-- Adversarial search (v141) on the isolated lemma: requirement systems "y@t ⇒ r@i", all their solutions
-- as a state with exact tables, every map pin; look for ghosts the base review leaves undetectable
-- (a counterexample to GhostsLine) or that survive the full review (a counterexample to FilterSlices)
-- ============================================================

structure AdvScore where
  finalCE : Nat := 0     -- ghosts surviving the full review
  baseCE : Nat := 0      -- ghosts after the base review, symmetric and sharing every step
  baseGhosts : Nat := 0  -- ghosts after the base review (search signal)
  deriving Repr

def AdvScore.value (a : AdvScore) : Nat := 1000000 * a.finalCE + 1000 * a.baseCE + a.baseGhosts

/-- The node ids of a map path's single-path state. -/
def pathIds (p : List NodeId) : List PathNodeId :=
  (List.range p.length).map (fun i =>
    { id := p[i]!, parent_id := if i == 0 then none else some p[i - 1]! })

def advEval (steps width : Nat) (reqs : List (NodeId × NodeId)) : AdvScore := Id.run do
  let mut all : List (List NodeId) := [[]]
  for sIdx in [0:steps] do
    let choices : List Nat := if sIdx + 1 == steps then [0] else List.range width
    all := all.flatMap (fun p => choices.map (fun i => p ++ [⟨(sIdx : Int), (i : Int)⟩]))
  let ok (p : List NodeId) : Bool := reqs.all (fun (a, b) => !(p.contains a) || p.contains b)
  let sols := all.filter ok
  if sols.length < 2 then return {}
  let states := sols.map pathState
  let U := match states with | [] => GPathM.empty | g :: rest => rest.foldl join g
  if !isValid U then return {}
  let ids := sols.map pathIds
  let mut sc : AdvScore := {}
  for sIdx in [0:steps - 1] do
    for i in [0:width] do
      let pin : NodeId := ⟨(sIdx : Int), (i : Int)⟩
      let through := (sols.zip ids).filter (fun (p, _) => p.contains pin)
      let onPath (x v : PathNodeId) : Bool := through.any (fun (_, q) => q.contains x && q.contains v)
      let P := [pin].foldl filterRequire U
      let B := review P
      let R := filterAllAgg U [pin]
      if isValid B then
        for n in B.nodes do
          for v in n.owners do
            if v == n.id then continue
            match B.node? v with
            | none => pure ()
            | some nv =>
              if onPath n.id v then continue
              sc := { sc with baseGhosts := sc.baseGhosts + 1 }
              if nv.owners.contains n.id && sharesEveryStep B.current_step n.owners nv.owners then
                sc := { sc with baseCE := sc.baseCE + 1 }
      if isValid R then
        for n in R.nodes do
          for v in n.owners do
            if v == n.id || (R.node? v).isNone then continue
            if !onPath n.id v then sc := { sc with finalCE := sc.finalCE + 1 }
  return sc

def advMutate (steps width : Nat) (reqs : List (NodeId × NodeId)) (rng0 : AbsSat.SatMachine.DiffTest.Rng) :
    List (NodeId × NodeId) × AbsSat.SatMachine.DiffTest.Rng := Id.run do
  let mut rng := rng0
  let (r1, op) := rng.below 3
  rng := r1
  let fresh : AbsSat.SatMachine.DiffTest.Rng → (NodeId × NodeId) × AbsSat.SatMachine.DiffTest.Rng := fun r => Id.run do
    let (a1, t) := r.below (steps - 2)
    let (a2, y) := a1.below width
    let (a3, i) := a2.below (t + 1)
    let (a4, rr) := a3.below width
    return ((⟨((t + 1 : Nat) : Int), (y : Int)⟩, ⟨(i : Int), (rr : Int)⟩), a4)
  if op == 0 || reqs.isEmpty then
    let (q, r2) := fresh rng
    return (reqs ++ [q], r2)
  else if op == 1 then
    let (r2, j) := rng.below reqs.length
    return (reqs.eraseIdx j, r2)
  else
    let (r2, j) := rng.below reqs.length
    let (q, r3) := fresh r2
    return (reqs.set j q, r3)

def runAdversarial (steps width iters restarts seed : Nat) : IO Unit := do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut bestEver : AdvScore := {}
  let mut evals := 0
  for rs in [0:restarts] do
    -- a random start
    let mut reqs : List (NodeId × NodeId) := []
    let (r0, n0) := rng.below (2 * steps)
    rng := r0
    for _ in [0:n0 + 1] do
      let (q, r1) := advMutate steps width [] rng
      rng := r1
      reqs := reqs ++ q
    let mut cur := advEval steps width reqs
    evals := evals + 1
    for _ in [0:iters] do
      let (cand, r2) := advMutate steps width reqs rng
      rng := r2
      let sc := advEval steps width cand
      evals := evals + 1
      if sc.value ≥ cur.value then
        reqs := cand
        cur := sc
      if sc.baseCE > 0 || sc.finalCE > 0 then
        IO.println s!"  COUNTEREXAMPLE restart {rs}: {repr sc} reqs={cand.map (fun (a, b) => ((a.step, a.index), (b.step, b.index)))}"
    if cur.value > bestEver.value then bestEver := cur
  IO.println s!"adversarial steps={steps} width={width} iters={iters} restarts={restarts} seed={seed}: evals={evals} best={repr bestEver}"

-- ============================================================
-- Sequential pins (v143): pinning a send's requirements all at once versus one by one, reviewing after
-- each, on every send of the run
-- ============================================================

def runSeqPin (φ : Cnf) : IO Unit := do
  let mut sends := 0
  let mut bothValid := 0
  let mut equal := 0
  let mut validDiffers := 0
  let mut differ := 0
  for line in aggLines φ do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let rq := reqOfCnf φ d
        if rq.length < 2 then continue
        sends := sends + 1
        let w := filterWeakAll kv.2 (weakReqOfCnf φ d)
        let all := filterAllAgg w rq
        let seq := rq.foldl (fun g r => filterAllAgg g [r]) w
        let va := isValid all
        let vs := isValid seq
        if va != vs then
          validDiffers := validDiffers + 1
        else if va then
          bothValid := bothValid + 1
          let (xn, mn, xo, mo, xg, mg) := diffStates all seq
          if xn + mn + xo + mo + xg + mg == 0 then equal := equal + 1 else differ := differ + 1
  IO.println s!"seqpin: sends with ≥2 pins={sends} bothValid={bothValid} equal={equal} DIFFER={differ} VALIDITY_DIFFERS={validDiffers}"

-- ============================================================
-- v144: do the weak requirements change the tables, or only the cost?
-- ============================================================

def aggLinesNoWeak (φ : Cnf) : List PureLine := Id.run do
  let mut line := pureInit φ
  let mut out := [line]
  for _ in [0:(stepCount φ - 1).toNat] do
    line := line.foldl (fun next kv =>
      (mapSons φ kv.1.step kv.1.index).foldl (fun next d =>
        let h := up (filterAllAgg kv.2 (reqOfCnf φ d)) d ""
        if isValid h then insertPure next d h else next) next) []
    out := out ++ [line]
  return out

def runWeakCmp (φ : Cnf) : IO Unit := do
  -- per send, from the same state
  let mut sends := 0
  let mut bothValid := 0
  let mut equal := 0
  let mut differ := 0
  let mut validDiffers := 0
  for line in aggLines φ do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let rq := reqOfCnf φ d
        let ws := weakReqOfCnf φ d
        if ws.isEmpty then continue
        sends := sends + 1
        let a := filterAllAgg (filterWeakAll kv.2 ws) rq
        let b := filterAllAgg kv.2 rq
        if isValid a != isValid b then validDiffers := validDiffers + 1
        else if isValid a then
          bothValid := bothValid + 1
          let (xn, mn, xo, mo, xg, mg) := diffStates a b
          if xn + mn + xo + mo + xg + mg == 0 then equal := equal + 1 else differ := differ + 1
  IO.println s!"weakcmp per send: sends with weak reqs={sends} bothValid={bothValid} equal={equal} DIFFER={differ} VALIDITY_DIFFERS={validDiffers}"
  -- whole run, line by line
  let la := aggLines φ
  let lb := aggLinesNoWeak φ
  let mut lines := 0
  let mut keysDiffer := 0
  let mut states := 0
  let mut statesEqual := 0
  let mut statesDiffer := 0
  for (a, b) in la.zip lb do
    lines := lines + 1
    let ka := a.map (·.1)
    let kb := b.map (·.1)
    if !(ka.all (kb.contains ·) && kb.all (ka.contains ·)) then keysDiffer := keysDiffer + 1
    for kv in a do
      match b.find? (fun y => y.1 == kv.1) with
      | none => pure ()
      | some (_, h) =>
        states := states + 1
        let (xn, mn, xo, mo, xg, mg) := diffStates kv.2 h
        if xn + mn + xo + mo + xg + mg == 0 then statesEqual := statesEqual + 1 else statesDiffer := statesDiffer + 1
  IO.println s!"weakcmp whole run: lines={lines} KEYS_DIFFER={keysDiffer} states={states} equal={statesEqual} DIFFER={statesDiffer}"

-- ============================================================
-- v144: splicing two surviving paths at the middle node
-- ============================================================

structure SpliceStat where
  pins : Nat := 0
  -- index: 0 = kept & case A, 1 = kept & case B, 2 = removed & case A, 3 = removed & case B
  entries : Array Nat := #[0, 0, 0, 0]
  noPairs : Array Nat := #[0, 0, 0, 0]
  allValid : Array Nat := #[0, 0, 0, 0]
  someValid : Array Nat := #[0, 0, 0, 0]
  noneValid : Array Nat := #[0, 0, 0, 0]
  truth : Array Nat := #[0, 0, 0, 0]
  truncated : Nat := 0

def runSplice (φ : Cnf) (budget cap : Nat) (st0 : SpliceStat) : SpliceStat := Id.run do
  let mut st := st0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      let tbl : Std.HashMap PathNodeId PNodeM := G.nodes.foldl (fun acc m => acc.insert m.id m) {}
      let gow := Std.HashSet.ofList G.gowners
      let cs := G.current_step
      let mut sols : Array (List PathNodeId) := #[]
      let mut bud := budget
      for n in G.nodes.filter (fun n => n.id.id.step == cs - 1) do
        if !gow.contains n.id then continue
        let (a', b') := solWalk tbl gow [n.id] sols bud
        sols := a'
        bud := b'
      if bud == 0 then
        st := { st with truncated := st.truncated + 1 }
        continue
      let solSet : Std.HashSet (List PathNodeId) := Std.HashSet.ofList sols.toList
      let at_ (c : List PathNodeId) (k : Int) : Option PathNodeId := c[k.toNat]?
      let maps := (G.gowners.map (·.id)).eraseDups
      for m in maps do
        if m.step == cs - 1 then continue
        let R := filterAllAgg G [m]
        if !isValid R then continue
        st := { st with pins := st.pins + 1 }
        let rtbl : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc n => acc.insert n.id n) {}
        let passM (c : List PathNodeId) : Bool := match at_ c m.step with | some y => y.id == m | none => false
        for n in R.nodes do
          let x := n.id
          let gOwners := match tbl.get? x with | some g0 => g0.owners | none => []
          for q in gOwners do
            if !(q.id.step < x.id.step) then continue
            if !rtbl.contains q then continue
            if m.step == x.id.step || m.step == q.id.step then continue
            let kept := n.owners.contains q
            let caseB := q.id.step < m.step && m.step < x.id.step
            let idx := (if kept then 0 else 2) + (if caseB then 1 else 0)
            let passX (c : List PathNodeId) : Bool := at_ c x.id.step == some x
            let passQ (c : List PathNodeId) : Bool := at_ c q.id.step == some q
            -- the three points, top to bottom, and the splice step (the middle one)
            let (p1, p2, mid) :=
              if caseB then ((sols.toList.filter (fun c => passX c && passM c)).take cap,
                             (sols.toList.filter (fun c => passM c && passQ c)).take cap, m.step)
              else if m.step < q.id.step then ((sols.toList.filter (fun c => passX c && passQ c)).take cap,
                             (sols.toList.filter (fun c => passQ c && passM c)).take cap, q.id.step)
              else ((sols.toList.filter (fun c => passM c && passX c)).take cap,
                    (sols.toList.filter (fun c => passX c && passQ c)).take cap, x.id.step)
            let truth := sols.toList.any (fun c => passX c && passQ c && passM c)
            let mut tested := 0
            let mut valid := 0
            for a in p1 do
              for b in p2 do
                if at_ a mid != at_ b mid then continue
                tested := tested + 1
                let sp := b.take mid.toNat ++ a.drop mid.toNat
                if solSet.contains sp then valid := valid + 1
            let inc (arr : Array Nat) : Array Nat := arr.modify idx (· + 1)
            st := { st with entries := inc st.entries }
            if truth then st := { st with truth := inc st.truth }
            if tested == 0 then st := { st with noPairs := inc st.noPairs }
            else if valid == tested then st := { st with allValid := inc st.allValid }
            else if valid == 0 then st := { st with noneValid := inc st.noneValid }
            else st := { st with someValid := inc st.someValid }
  return st

def reportSplice (name : String) (st : SpliceStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} truncated={st.truncated} | {ms}ms"
  let labels := ["kept A (pin outside)", "kept B (pin between)", "removed A", "removed B"]
  for (l, i) in labels.zipIdx do
    IO.println s!"  {l}: entries={st.entries[i]!} truth={st.truth[i]!} noPairs={st.noPairs[i]!} allSplicesValid={st.allValid[i]!} someValid={st.someValid[i]!} noneValid={st.noneValid[i]!}"

-- ============================================================
-- v144: the greedy construction — from an entry (x, q) of a pinned reviewed state, fill the steps
-- below x (downward), then above x (upward), each time with a node that owns and is owned by every
-- node already chosen. Does it ever get stuck?
-- ============================================================

structure GreedyStat where
  pins : Nat := 0
  entries : Nat := 0
  firstOk : Nat := 0
  FIRST_STUCK : Nat := 0
  branches : Nat := 0
  stuckBranches : Nat := 0
  entriesWithStuckBranch : Nat := 0
  capped : Nat := 0
  ex : List String := []

/-- Exhaustive search in the fixed order; returns (complete branches, stuck branches, budget left). -/
partial def greedyAll (rtbl : Std.HashMap PathNodeId PNodeM) (byStep : Std.HashMap Int (List PathNodeId))
    (rel : PathNodeId → PathNodeId → Bool) (order : List Int) (chosen : List PathNodeId) (bud : Nat) :
    Nat × Nat × Nat :=
  match order with
  | [] => (1, 0, bud)
  | l :: rest => Id.run do
    if bud == 0 then return (0, 0, 0)
    let cands := (byStep.getD l []).filter (fun y => chosen.all (fun c => rel y c && rel c y))
    if cands.isEmpty then return (0, 1, bud - 1)
    let mut ok := 0
    let mut stuck := 0
    let mut b := bud - 1
    for y in cands do
      let (o, s, b') := greedyAll rtbl byStep rel rest (y :: chosen) b
      ok := ok + o
      stuck := stuck + s
      b := b'
      if b == 0 then break
    return (ok, stuck, b)

def greedyFirst (byStep : Std.HashMap Int (List PathNodeId)) (rel : PathNodeId → PathNodeId → Bool)
    (order : List Int) (chosen : List PathNodeId) : Bool := Id.run do
  let mut ch := chosen
  for l in order do
    match (byStep.getD l []).find? (fun y => ch.all (fun c => rel y c && rel c y)) with
    | some y => ch := y :: ch
    | none => return false
  return true

def runGreedy (φ : Cnf) (budget sample : Nat) (st0 : GreedyStat) : GreedyStat := Id.run do
  let mut st := st0
  let mut tick := 0
  for line in aggLines φ do
    for kv in line do
      let G := filterAllAgg kv.2 []
      if !isValid G then continue
      let cs := G.current_step
      let maps := (G.gowners.map (·.id)).eraseDups
      for m in maps do
        if m.step == cs - 1 then continue
        let R := filterAllAgg G [m]
        if !isValid R then continue
        st := { st with pins := st.pins + 1 }
        let rtbl : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc n => acc.insert n.id n) {}
        let gow := Std.HashSet.ofList R.gowners
        let byStep : Std.HashMap Int (List PathNodeId) := R.nodes.foldl (fun acc n =>
          if gow.contains n.id then acc.insert n.id.id.step (n.id :: acc.getD n.id.id.step []) else acc) {}
        let rel (a b : PathNodeId) : Bool := match rtbl.get? a with
          | some n => n.owners.contains b && rtbl.contains b
          | none => false
        for n in R.nodes do
          let x := n.id
          for q in n.owners do
            if !(q.id.step < x.id.step) then continue
            if !rtbl.contains q then continue
            tick := tick + 1
            if tick % sample != 0 then continue
            st := { st with entries := st.entries + 1 }
            let down := ((List.range x.id.step.toNat).reverse.map (fun (i : Nat) => (i : Int))).filter (· != q.id.step)
            let up := ((List.range (cs - 1 - x.id.step).toNat).map (fun (i : Nat) => x.id.step + 1 + (i : Int)))
            let order := down ++ up
            if greedyFirst byStep rel order [x, q] then st := { st with firstOk := st.firstOk + 1 }
            else
              st := { st with FIRST_STUCK := st.FIRST_STUCK + 1 }
              if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"first-choice stuck: x={x.id.step}.{x.id.index} q={q.id.step}.{q.id.index} pin={m.step}.{m.index}"] }
            let (o, s, b) := greedyAll rtbl byStep rel order [x, q] budget
            st := { st with branches := st.branches + o, stuckBranches := st.stuckBranches + s }
            if s > 0 then st := { st with entriesWithStuckBranch := st.entriesWithStuckBranch + 1 }
            if b == 0 then st := { st with capped := st.capped + 1 }
  return st

def reportGreedy (name : String) (st : GreedyStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} entries={st.entries} firstChoiceOk={st.firstOk} FIRST_STUCK={st.FIRST_STUCK} | exhaustive: completeBranches={st.branches} stuckBranches={st.stuckBranches} entriesWithAStuckBranch={st.entriesWithStuckBranch} capped={st.capped} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v144: PinExtends — in every valid state the reader can reach from a valid final state, every step
-- admits a pin that keeps it valid. Walks: pin a random unpinned step with a random valid choice.
-- ============================================================

structure PxStat where
  finals : Nat := 0
  validFinals : Nat := 0
  walks : Nat := 0
  statesChecked : Nat := 0
  stepChecks : Nat := 0
  FAIL : Nat := 0
  walksComplete : Nat := 0
  ex : List String := []

def pxNext (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

def runPinExt (φ : Cnf) (walksPer : Nat) (seed : Nat) (st0 : PxStat) : PxStat := Id.run do
  let mut st := st0
  let mut rnd := seed
  let finals := (aggLines φ).getLast?.getD []
  for kv in finals do
    st := { st with finals := st.finals + 1 }
    let g0 := filterAllAgg kv.2 []
    if !isValid g0 then continue
    st := { st with validFinals := st.validFinals + 1 }
    let cs := g0.current_step
    let steps : List Int := (List.range cs.toNat).map (fun (i : Nat) => (i : Int))
    for _ in [0:walksPer] do
      st := { st with walks := st.walks + 1 }
      let mut S := g0
      let mut unpinned := steps
      let mut ok := true
      while ok && !unpinned.isEmpty do
        st := { st with statesChecked := st.statesChecked + 1 }
        -- every step must admit a valid pin
        let mut choices : List (Int × List NodeId) := []
        for l in steps do
          st := { st with stepChecks := st.stepChecks + 1 }
          let ids := ((S.gowners.filter (·.id.step == l)).map (·.id)).eraseDups
          let good := ids.filter (fun m => isValid (filterAllAgg S [m]))
          if good.isEmpty then
            st := { st with FAIL := st.FAIL + 1 }
            if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"no valid pin at step {l} (state key {kv.1.step}.{kv.1.index}, {steps.length - unpinned.length} pins so far)"] }
            ok := false
          choices := choices ++ [(l, good)]
        if !ok then break
        -- pin a random unpinned step with a random valid choice
        rnd := pxNext rnd
        let l := unpinned[rnd % unpinned.length]!
        let good := (choices.find? (·.1 == l)).map (·.2) |>.getD []
        rnd := pxNext rnd
        let m := good[rnd % good.length]!
        S := filterAllAgg S [m]
        unpinned := unpinned.filter (· != l)
      if ok then st := { st with walksComplete := st.walksComplete + 1 }
  return st

def reportPx (name : String) (st : PxStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: finals={st.finals} validFinals={st.validFinals} walks={st.walks} complete={st.walksComplete} statesChecked={st.statesChecked} stepChecks={st.stepChecks} FAIL={st.FAIL} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v145: PinExtends bottom-up — pin steps 0, 1, 2, … in order; at each step try every live map node.
-- Kinds: 0 = variable (even, < litBlock), 1 = negation (odd, < litBlock), 2 = clause/fusion.
-- ============================================================

structure PinUpStat where
  walks : Nat := 0
  complete : Nat := 0
  -- per kind
  steps : Array Nat := #[0, 0, 0]
  single : Array Nat := #[0, 0, 0]      -- steps where only one live map node is left
  cands : Array Nat := #[0, 0, 0]
  candFail : Array Nat := #[0, 0, 0]
  NO_VALID : Array Nat := #[0, 0, 0]
  ex : List String := []

def runPinUp (φ : Cnf) (walksPer : Nat) (seed : Nat) (st0 : PinUpStat) : PinUpStat := Id.run do
  let mut st := st0
  let mut rnd := seed
  let finals := (aggLines φ).getLast?.getD []
  for kv in finals do
    let g0 := filterAllAgg kv.2 []
    if !isValid g0 then continue
    let cs := g0.current_step
    for _ in [0:walksPer] do
      st := { st with walks := st.walks + 1 }
      let mut S := g0
      let mut ok := true
      for i in [0:cs.toNat] do
        let l : Int := i
        let kind := if l < litBlock φ then (if l % 2 == 0 then 0 else 1) else 2
        let ids := ((S.gowners.filter (·.id.step == l)).map (·.id)).eraseDups
        st := { st with steps := st.steps.modify kind (· + 1) }
        if ids.length == 1 then st := { st with single := st.single.modify kind (· + 1) }
        let good := ids.filter (fun m => isValid (filterAllAgg S [m]))
        st := { st with cands := st.cands.modify kind (· + ids.length),
                        candFail := st.candFail.modify kind (· + (ids.length - good.length)) }
        if good.isEmpty then
          st := { st with NO_VALID := st.NO_VALID.modify kind (· + 1) }
          if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"no valid pin at step {l} kind {kind} ({ids.length} live map nodes)"] }
          ok := false
          break
        rnd := pxNext rnd
        S := filterAllAgg S [good[rnd % good.length]!]
      if ok then st := { st with complete := st.complete + 1 }
  return st

def reportPinUp (name : String) (st : PinUpStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: walks={st.walks} complete={st.complete} | {ms}ms"
  for (l, k) in ["variable", "negation", "clause/fusion"].zipIdx do
    IO.println s!"  {l}: steps={st.steps[k]!} singleLive={st.single[k]!} candidates={st.cands[k]!} candidatesFailing={st.candFail[k]!} NO_VALID={st.NO_VALID[k]!}"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v146: is Sa (the nodes owning the live value a, with the tables restricted to them) already a support?
-- Bottom-up walks; at each variable step with the prefix decided, for each live value a.
-- ============================================================

structure TaStat where
  cases : Nat := 0
  saNodes : Nat := 0
  COV_FAIL : Nat := 0
  AGG_FAIL : Nat := 0
  PAR_FAIL : Nat := 0
  SON_FAIL : Nat := 0
  casesClean : Nat := 0
  ex : List String := []

def runTripleA (φ : Cnf) (walksPer : Nat) (seed : Nat) (st0 : TaStat) : TaStat := Id.run do
  let mut st := st0
  let mut rnd := seed
  let finals := (aggLines φ).getLast?.getD []
  for kv in finals do
    let g0 := filterAllAgg kv.2 []
    if !isValid g0 then continue
    let cs := g0.current_step
    for _ in [0:walksPer] do
      let mut S := g0
      for i in [0:cs.toNat] do
        let l : Int := i
        let isVar := l < litBlock φ && l % 2 == 0
        let ids := ((S.gowners.filter (·.id.step == l)).map (·.id)).eraseDups
        if isVar then
          let tbl : Std.HashMap PathNodeId PNodeM := S.nodes.foldl (fun acc n => acc.insert n.id n) {}
          let owns (x y : PathNodeId) : Bool := match tbl.get? x with
            | some n => n.owners.contains y && tbl.contains y
            | none => false
          for a in (S.nodes.filter (·.id.id.step == l)).map (·.id) do
            st := { st with cases := st.cases + 1 }
            let sa := (S.nodes.map (·.id)).filter (fun x => owns x a)
            let saSet := Std.HashSet.ofList sa
            st := { st with saNodes := st.saNodes + sa.length }
            let mut clean := true
            for x in sa do
              let xn := tbl.get! x
              let xo := xn.owners.filter (fun y => saSet.contains y)
              -- cov
              for k in [0:cs.toNat] do
                if !xo.any (·.id.step == (k : Int)) then
                  st := { st with COV_FAIL := st.COV_FAIL + 1 }; clean := false
              for y in xo do
                -- agg
                let yo := (tbl.get! y).owners
                for k in [0:cs.toNat] do
                  if !xo.any (fun z => z.id.step == (k : Int) && yo.contains z) then
                    st := { st with AGG_FAIL := st.AGG_FAIL + 1 }; clean := false
                    if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"agg: x={x.id.step}.{x.id.index} y={y.id.step}.{y.id.index} step {k} a={a.id.step}.{a.id.index}"] }
                -- par
                if x.parent_id.isSome then
                  if !xn.parents.any (fun c => saSet.contains c && owns x c && owns c x && owns c y) then
                    st := { st with PAR_FAIL := st.PAR_FAIL + 1 }; clean := false
                -- son
                if x.id.step != cs - 1 then
                  let sons := S.nodes.filter (fun m => m.parents.contains x)
                  if !sons.any (fun m => saSet.contains m.id && owns x m.id && owns m.id x && owns m.id y) then
                    st := { st with SON_FAIL := st.SON_FAIL + 1 }; clean := false
            if clean then st := { st with casesClean := st.casesClean + 1 }
        let good := ids.filter (fun m => isValid (filterAllAgg S [m]))
        if good.isEmpty then break
        rnd := pxNext rnd
        S := filterAllAgg S [good[rnd % good.length]!]
  return st

def reportTa (name : String) (st : TaStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: cases={st.cases} clean={st.casesClean} saNodes={st.saNodes} COV_FAIL={st.COV_FAIL} AGG_FAIL={st.AGG_FAIL} PAR_FAIL={st.PAR_FAIL} SON_FAIL={st.SON_FAIL} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v146: at the driver's joins, is each entry of the reviewed join carried by the tables of the side of
-- one of its top anchors?
-- ============================================================

structure SideStat where
  joins : Nat := 0
  topsShared : Nat := 0
  entries : Nat := 0
  inA : Nat := 0
  inB : Nat := 0
  inBoth : Nat := 0
  sideOk : Nat := 0          -- in the tables of a side where it has a common top anchor
  crossOnly : Nat := 0       -- only anchors on the side whose tables lack the entry
  NO_ANCHOR : Nat := 0
  crossAnchor : Nat := 0     -- has some anchor on a side whose tables lack the entry
  onlyA_bothNodes : Nat := 0 -- entry only in a, x and v nodes of both sides
  ex : List String := []

def sideCheck (a b : GPathM) (st0 : SideStat) : SideStat := Id.run do
  let mut st := st0
  let R := reviewAgg (join a b)
  if !isValid R then return st
  st := { st with joins := st.joins + 1 }
  let cs := R.current_step
  let tA : Std.HashMap PathNodeId PNodeM := a.nodes.foldl (fun acc n => acc.insert n.id n) {}
  let tB : Std.HashMap PathNodeId PNodeM := b.nodes.foldl (fun acc n => acc.insert n.id n) {}
  let tR : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc n => acc.insert n.id n) {}
  let tops := (R.nodes.filter (·.id.id.step == cs - 1)).map (·.id)
  for z in tops do
    if tA.contains z && tB.contains z then st := { st with topsShared := st.topsShared + 1 }
  let ownsIn (t : Std.HashMap PathNodeId PNodeM) (x y : PathNodeId) : Bool :=
    match t.get? x with | some n => n.owners.contains y | none => false
  for n in R.nodes do
    let x := n.id
    for v in n.owners do
      if !tR.contains v then continue
      st := { st with entries := st.entries + 1 }
      let ia := ownsIn tA x v
      let ib := ownsIn tB x v
      if ia then st := { st with inA := st.inA + 1 }
      if ib then st := { st with inB := st.inB + 1 }
      if ia && ib then st := { st with inBoth := st.inBoth + 1 }
      let anchors := tops.filter (fun z => ownsIn tR x z && ownsIn tR v z)
      let ancA := anchors.any (fun z => tA.contains z)
      let ancB := anchors.any (fun z => tB.contains z)
      if (ancA && !ia) || (ancB && !ib) then st := { st with crossAnchor := st.crossAnchor + 1 }
      if (ia != ib) && tA.contains x && tB.contains x && tA.contains v && tB.contains v then
        st := { st with onlyA_bothNodes := st.onlyA_bothNodes + 1 }
      if anchors.isEmpty then st := { st with NO_ANCHOR := st.NO_ANCHOR + 1 }
      else if (ia && ancA) || (ib && ancB) then st := { st with sideOk := st.sideOk + 1 }
      else
        st := { st with crossOnly := st.crossOnly + 1 }
        if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"cross: x={x.id.step}.{x.id.index} v={v.id.step}.{v.id.index} inA={ia} inB={ib} ancA={ancA} ancB={ancB}"] }
  return st

def runSideCls (φ : Cnf) (st0 : SideStat) : SideStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  let pinned (g : GPathM) (d : NodeId) : GPathM :=
    (reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              st := sideCheck e hst st
              for d' in mapSons φ d.step d.index do
                st := sideCheck (pinned e d') (pinned hst d') st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportSide (name : String) (st : SideStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} topsShared={st.topsShared} entries={st.entries} inA={st.inA} inB={st.inB} inBoth={st.inBoth} sideOk={st.sideOk} CROSS_ONLY={st.crossOnly} NO_ANCHOR={st.NO_ANCHOR} crossAnchor={st.crossAnchor} oneSideEntryNodesInBoth={st.onlyA_bothNodes} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v147: SurvivorsRealized — each entry of the reviewed join carried by a side lies on a path of that
-- (pinned) side.
-- ============================================================

structure SrStat where
  joins : Nat := 0
  entries : Nat := 0
  realized : Nat := 0
  NOT_REALIZED : Nat := 0
  truncated : Nat := 0
  rEntries : Nat := 0
  eitherOk : Nat := 0
  NEITHER : Nat := 0
  ex : List String := []

def sidePaths (a : GPathM) (budget : Nat) : Option (Array (List PathNodeId)) := Id.run do
  let tbl : Std.HashMap PathNodeId PNodeM := a.nodes.foldl (fun acc m => acc.insert m.id m) {}
  let gow := Std.HashSet.ofList a.gowners
  let cs := a.current_step
  let mut sols : Array (List PathNodeId) := #[]
  let mut bud := budget
  for n in a.nodes.filter (fun n => n.id.id.step == cs - 1) do
    if !gow.contains n.id then continue
    let (s', b') := solWalk tbl gow [n.id] sols bud
    sols := s'
    bud := b'
  if bud == 0 then return none
  return some sols

def survCheck (a b : GPathM) (budget : Nat) (st0 : SrStat) : SrStat := Id.run do
  let mut st := st0
  let R := reviewAgg (join a b)
  if !isValid R then return st
  st := { st with joins := st.joins + 1 }
  let tR : Std.HashMap PathNodeId PNodeM := R.nodes.foldl (fun acc n => acc.insert n.id n) {}
  -- every entry of R on a path of one of the sides
  match sidePaths a budget, sidePaths b budget with
  | some sa, some sb =>
    for n in R.nodes do
      for v in n.owners do
        if !tR.contains v then continue
        st := { st with rEntries := st.rEntries + 1 }
        let x := n.id
        if sa.any (fun c => c.contains x && c.contains v) || sb.any (fun c => c.contains x && c.contains v) then
          st := { st with eitherOk := st.eitherOk + 1 }
        else
          st := { st with NEITHER := st.NEITHER + 1 }
          if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"neither: x={x.id.step}.{x.id.index} v={v.id.step}.{v.id.index}"] }
  | _, _ => st := { st with truncated := st.truncated + 1 }
  for S in [a, b] do
    match sidePaths S budget with
    | none => st := { st with truncated := st.truncated + 1 }
    | some sols =>
      let tS : Std.HashMap PathNodeId PNodeM := S.nodes.foldl (fun acc n => acc.insert n.id n) {}
      for n in R.nodes do
        let x := n.id
        match tS.get? x with
        | none => pure ()
        | some sx =>
          for v in n.owners do
            if !tR.contains v || !sx.owners.contains v || !tS.contains v then continue
            st := { st with entries := st.entries + 1 }
            let ok := sols.any (fun c => c.contains x && c.contains v)
            if ok then st := { st with realized := st.realized + 1 }
            else
              st := { st with NOT_REALIZED := st.NOT_REALIZED + 1 }
              pure ()
  return st

def runSurv (φ : Cnf) (budget : Nat) (st0 : SrStat) : SrStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  let pinned (g : GPathM) (d : NodeId) : GPathM :=
    (reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              for d' in mapSons φ d.step d.index do
                st := survCheck (pinned e d') (pinned hst d') budget st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportSurv (name : String) (st : SrStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} entries={st.entries} realized={st.realized} NOT_REALIZED={st.NOT_REALIZED} truncatedSides={st.truncated} | R entries={st.rEntries} onASidePath={st.eitherOk} NEITHER={st.NEITHER} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v148: NoBorrow — every path of the reviewed union of the pinned sides is a path of one side.
-- ============================================================

structure NbStat where
  joins : Nat := 0
  paths : Nat := 0
  onA : Nat := 0
  onB : Nat := 0
  BORROWED : Nat := 0
  truncated : Nat := 0
  plainJoins : Nat := 0
  plainPaths : Nat := 0
  PLAIN_BORROWED : Nat := 0
  ex : List String := []

def nbCheck (a b : GPathM) (budget : Nat) (st0 : NbStat) : NbStat := Id.run do
  let mut st := st0
  -- the plain (unreviewed) union
  let J := join a b
  match sidePaths J budget, sidePaths a budget, sidePaths b budget with
  | some pj, some pa, some pb =>
    st := { st with plainJoins := st.plainJoins + 1 }
    let sa : Std.HashSet (List PathNodeId) := Std.HashSet.ofList pa.toList
    let sb : Std.HashSet (List PathNodeId) := Std.HashSet.ofList pb.toList
    for c in pj do
      st := { st with plainPaths := st.plainPaths + 1 }
      if !sa.contains c && !sb.contains c then st := { st with PLAIN_BORROWED := st.PLAIN_BORROWED + 1 }
  | _, _, _ => pure ()
  let R := reviewAgg (join a b)
  if !isValid R then return st
  st := { st with joins := st.joins + 1 }
  match sidePaths R budget, sidePaths a budget, sidePaths b budget with
  | some pr, some pa, some pb =>
    let sa : Std.HashSet (List PathNodeId) := Std.HashSet.ofList pa.toList
    let sb : Std.HashSet (List PathNodeId) := Std.HashSet.ofList pb.toList
    for c in pr do
      st := { st with paths := st.paths + 1 }
      let ia := sa.contains c
      let ib := sb.contains c
      if ia then st := { st with onA := st.onA + 1 }
      if ib then st := { st with onB := st.onB + 1 }
      if !ia && !ib then
        st := { st with BORROWED := st.BORROWED + 1 }
        if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"borrowed path of length {c.length}"] }
  | _, _, _ => st := { st with truncated := st.truncated + 1 }
  return st

def runNoBorrow (φ : Cnf) (budget : Nat) (st0 : NbStat) : NbStat := Id.run do
  let mut st := st0
  let mut line := pureInit φ
  let pinned (g : GPathM) (d : NodeId) : GPathM :=
    (reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))
  let send (g : GPathM) (d : NodeId) : GPathM :=
    up (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
  for _ in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let hst := send kv.2 d
        if isValid hst then
          match next.find? (fun x => x.1 == d) with
          | some (_, e) =>
            if okJoin e hst then
              for d' in mapSons φ d.step d.index do
                st := nbCheck (pinned e d') (pinned hst d') budget st
          | none => pure ()
          next := insertPure next d hst
    line := next
  return st

def reportNb (name : String) (st : NbStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} pathsOfReviewedUnion={st.paths} onSideA={st.onA} onSideB={st.onB} BORROWED={st.BORROWED} truncated={st.truncated} | plain union: joins={st.plainJoins} paths={st.plainPaths} BORROWED={st.PLAIN_BORROWED} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- v148: EntryPin — pinning the map nodes of both ends of an entry and of their parents keeps a
-- reader's state valid. Bottom-up walks from the final states; entries sampled.
-- ============================================================

structure EpStat where
  states : Nat := 0
  entries : Nat := 0
  valid : Nat := 0
  INVALID : Nat := 0
  ex : List String := []

def runEntryPin (φ : Cnf) (walksPer sample seed : Nat) (st0 : EpStat) : EpStat := Id.run do
  let mut st := st0
  let mut rnd := seed
  let mut tick := 0
  let finals := (aggLines φ).getLast?.getD []
  for kv in finals do
    let g0 := filterAllAgg kv.2 []
    if !isValid g0 then continue
    let cs := g0.current_step
    for _ in [0:walksPer] do
      let mut S := g0
      for i in [0:cs.toNat] do
        st := { st with states := st.states + 1 }
        let tS : Std.HashMap PathNodeId PNodeM := S.nodes.foldl (fun acc n => acc.insert n.id n) {}
        for n in S.nodes do
          for q in n.owners do
            if !tS.contains q then continue
            tick := tick + 1
            if tick % sample != 0 then continue
            let x := n.id
            let pins := [x.id, q.id] ++ x.parent_id.toList ++ q.parent_id.toList
            st := { st with entries := st.entries + 1 }
            if isValid (pins.foldl (fun g r => filterAllAgg g [r]) S) then st := { st with valid := st.valid + 1 }
            else
              st := { st with INVALID := st.INVALID + 1 }
              if st.ex.length < 5 then st := { st with ex := st.ex ++ [s!"x={x.id.step}.{x.id.index} q={q.id.step}.{q.id.index} after {i} steps pinned"] }
        let l : Int := i
        let ids := ((S.gowners.filter (·.id.step == l)).map (·.id)).eraseDups
        let good := ids.filter (fun m => isValid (filterAllAgg S [m]))
        if good.isEmpty then break
        rnd := pxNext rnd
        S := filterAllAgg S [good[rnd % good.length]!]
  return st

def reportEp (name : String) (st : EpStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: states={st.states} entries={st.entries} valid={st.valid} INVALID={st.INVALID} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

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

-- ============================================================
-- PinCommutes (report v153): at every clause-row send of a branch, every entry towards a literal of the
-- pinned, reviewed state is an entry of the branch that also carries the row's pins, same key.
-- ============================================================

def restrictP (P : List NodeId) (k : Int) (line : PureLine) : PureLine :=
  line.filter (fun kv => P.all (fun r => r.step != k || kv.1 == r))

/-- The lines of the branch of `P` (`PinHistory.branchLine`), steps `0 …`. -/
def branchLinesP (φ : Cnf) (P : List NodeId) : Array PureLine := Id.run do
  let mut line := restrictP P 0 (pureInit φ)
  let mut out := #[line]
  for i in [0:(stepCount φ - 1).toNat] do
    line := restrictP P (Int.ofNat i + 1) (advanceLine φ line)
    out := out.push line
  return out

structure PCStat where
  branches : Nat := 0
  sends : Nat := 0
  entries : Nat := 0
  missingKey : Nat := 0
  violations : Nat := 0
  ex : List String := []

def runPinCommute (φ : Cnf) (depth : Nat) (st0 : PCStat) : PCStat := Id.run do
  let mut st := st0
  let mut cache : Std.HashMap (List NodeId) (Array PureLine) := {}
  let mut todo : List (List NodeId × Nat) := [([], 1)]
  let mut seen : Std.HashSet (List NodeId) := {}
  let lb : Int := 2 * (φ.nVars : Int)
  while !todo.isEmpty do
    let (P, lvl) := todo.head!
    todo := todo.tail!
    if seen.contains P then continue
    seen := seen.insert P
    st := { st with branches := st.branches + 1 }
    let lines ← match cache.get? P with
      | some l => pure l
      | none => pure (branchLinesP φ P)
    cache := cache.insert P lines
    for m in [0:lines.size - 1] do
      for kv in lines[m]! do
        for d in mapSons φ kv.1.step kv.1.index do
          let R := reqOfCnf φ d
          if d.step ≤ lb || R.isEmpty then continue
          let A := filterAllAgg kv.2 R
          if !isValid A then continue
          st := { st with sends := st.sends + 1 }
          let Q := P ++ R
          let linesQ ← match cache.get? Q with
            | some l => pure l
            | none => pure (branchLinesP φ Q)
          cache := cache.insert Q linesQ
          if lvl < depth then todo := todo ++ [(Q, lvl + 1)]
          let kv' := (linesQ[m]!).find? (fun e => e.1 == kv.1)
          let memA : Std.HashSet PathNodeId := Std.HashSet.ofList (A.nodes.map (·.id))
          let tQ : Std.HashMap PathNodeId (Std.HashSet PathNodeId) := match kv' with
            | some e => e.2.nodes.foldl (fun acc n => acc.insert n.id (Std.HashSet.ofList n.owners)) {}
            | none => {}
          if kv'.isNone then st := { st with missingKey := st.missingKey + 1 }
          for n in A.nodes do
            for q in n.owners do
              if !memA.contains q then continue
              if !(q.id.step < lb || q.id.step == 0) then continue
              st := { st with entries := st.entries + 1 }
              let ok := match tQ.get? n.id, tQ.get? q with
                | some o, some _ => o.contains q
                | _, _ => false
              if !ok then
                st := { st with violations := st.violations + 1 }
                if st.ex.length < 8 then
                  st := { st with ex := st.ex ++ [s!"step {m} key {kv.1.step}.{kv.1.index} row {d.step}.{d.index} |P|={P.length}: {n.id.id.step}.{n.id.id.index} -> {q.id.step}.{q.id.index}"] }
  return st

def reportPC (name : String) (st : PCStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: branches={st.branches} clauseSends={st.sends} entries={st.entries} MISSING_KEY={st.missingKey} VIOLATIONS={st.violations} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


-- One pin at a time, at every line: `filterAllAgg G [r]` inside the branch `[r]` state with the same key.
structure P1Stat where
  pins : Nat := 0
  valid : Nat := 0
  missingKey : Nat := 0
  badNodes : Nat := 0
  badEntries : Nat := 0
  badStatesVar : Nat := 0
  badStatesClause : Nat := 0
  ex : List String := []

def runPin1 (φ : Cnf) (st0 : P1Stat) : P1Stat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  let mut cache : Std.HashMap NodeId (Array PureLine) := {}
  for m in [0:lines.size] do
    for kv in lines[m]! do
      let G := kv.2
      let ids := ((G.gowners.filter (fun q => q.id.step < lb || q.id.step == 0)).map (·.id)).eraseDups
      for r in ids do
        if r.step ≥ Int.ofNat m then continue
        st := { st with pins := st.pins + 1 }
        let A := filterAllAgg G [r]
        if !isValid A then continue
        st := { st with valid := st.valid + 1 }
        let bl ← match cache.get? r with
          | some l => pure l
          | none => pure (branchLinesP φ [r])
        cache := cache.insert r bl
        match (bl[m]!).find? (fun e => e.1 == kv.1) with
        | none =>
          st := { st with missingKey := st.missingKey + 1 }
          if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"MISSING KEY line {m} key {kv.1.step}.{kv.1.index} pin {r.step}.{r.index}"] }
        | some e =>
          let memB : Std.HashSet PathNodeId := Std.HashSet.ofList (e.2.nodes.map (·.id))
          let memA : Std.HashSet PathNodeId := Std.HashSet.ofList (A.nodes.map (·.id))
          let tB : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
            e.2.nodes.foldl (fun acc n => acc.insert n.id (Std.HashSet.ofList n.owners)) {}
          let mut bn := 0
          let mut be := 0
          for n in A.nodes do
            match tB.get? n.id with
            | none => bn := bn + 1
            | some o =>
              for q in n.owners do
                if memA.contains q && !o.contains q then be := be + 1
          if bn + be > 0 then
            st := { st with badNodes := st.badNodes + bn, badEntries := st.badEntries + be }
            if Int.ofNat m ≤ lb then st := { st with badStatesVar := st.badStatesVar + 1 }
            else st := { st with badStatesClause := st.badStatesClause + 1 }
            if st.ex.length < 8 then
              st := { st with ex := st.ex ++ [s!"line {m} key {kv.1.step}.{kv.1.index} pin {r.step}.{r.index}: nodes {bn} entries {be}"] }
          let _ := memB
  return st

def reportP1 (name : String) (st : P1Stat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} valid={st.valid} MISSING_KEY={st.missingKey} BAD_NODES={st.badNodes} BAD_ENTRIES={st.badEntries} badStates(var stage)={st.badStatesVar} badStates(clause stage)={st.badStatesClause} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


-- Base case of the one-pin commutation: a line state J (key p) is the join of the sends from the keys of
-- the previous line; pin one of those keys r (step just below the top). Compare the reviewed pinned join
-- with the send from r alone.
structure BJStat where
  joins : Nat := 0
  pins : Nat := 0
  valid : Nat := 0
  foreignPre : Nat := 0
  foreignNodeDies : Nat := 0
  foreignEntryDies : Nat := 0
  foreignSurvives : Nat := 0
  badNodes : Nat := 0
  badEntries : Nat := 0
  ex : List String := []

def ownerTable (g : GPathM) : Std.HashMap PathNodeId (Std.HashSet PathNodeId) :=
  g.nodes.foldl (fun acc n => acc.insert n.id (Std.HashSet.ofList n.owners)) {}

def runBaseJoin (φ : Cnf) (st0 : BJStat) : BJStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      st := { st with joins := st.joins + 1 }
      let tJ := ownerTable kv.2
      for (r, Sr) in sides do
        if r.step ≥ 2 * (φ.nVars : Int) then continue
        st := { st with pins := st.pins + 1 }
        let X := filterAllAgg kv.2 [r]
        let tR := ownerTable Sr
        let tX := ownerTable X
        -- foreign entries before the review: both ends are nodes of Sr, the entry is in J but not in Sr
        let mut foreign : List (PathNodeId × PathNodeId) := []
        for n in kv.2.nodes do
          match tR.get? n.id with
          | none => pure ()
          | some o =>
            for q in n.owners do
              if tR.contains q && !o.contains q then foreign := (n.id, q) :: foreign
        st := { st with foreignPre := st.foreignPre + foreign.length }
        if !isValid X then continue
        st := { st with valid := st.valid + 1 }
        for (x, q) in foreign do
          match tX.get? x with
          | none => st := { st with foreignNodeDies := st.foreignNodeDies + 1 }
          | some o =>
            if !tX.contains q then st := { st with foreignNodeDies := st.foreignNodeDies + 1 }
            else if o.contains q then
              st := { st with foreignSurvives := st.foreignSurvives + 1 }
              if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index}: {x.id.step}.{x.id.index} -> {q.id.step}.{q.id.index}"] }
            else st := { st with foreignEntryDies := st.foreignEntryDies + 1 }
        -- the full comparison: X inside Sr
        for n in X.nodes do
          match tR.get? n.id with
          | none => st := { st with badNodes := st.badNodes + 1 }
          | some o =>
            for q in n.owners do
              if tX.contains q && !o.contains q then st := { st with badEntries := st.badEntries + 1 }
      let _ := tJ
  return st

def reportBJ (name : String) (st : BJStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} pins={st.pins} valid={st.valid} | foreign entries before review={st.foreignPre}: an end dies={st.foreignNodeDies}, entry dies={st.foreignEntryDies}, SURVIVE={st.foreignSurvives} | X outside Sr: nodes={st.badNodes} entries={st.badEntries} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


-- Why a foreign entry dies: test the review's conditions for it against the final tables of X.
structure BWStat where
  foreign : Nat := 0
  aggFails : Nat := 0
  aggBelowPin : Nat := 0
  aggAtPin : Nat := 0
  aggAbovePin : Nat := 0
  parFails : Nat := 0
  sonFails : Nat := 0
  noneFails : Nat := 0
  ex : List String := []

def runBaseWhy (φ : Cnf) (st0 : BWStat) : BWStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      for (r, Sr) in sides do
        let X := filterAllAgg kv.2 [r]
        if !isValid X then continue
        let tR := ownerTable Sr
        let tX := ownerTable X
        let nodesX : Std.HashMap PathNodeId PNodeM := X.nodes.foldl (fun acc n => acc.insert n.id n) {}
        let owns (a b : PathNodeId) : Bool := match tX.get? a with | some o => o.contains b | none => false
        let cs := X.current_step
        for n in kv.2.nodes do
          match tR.get? n.id, tX.get? n.id with
          | some o, some _ =>
            for q in n.owners do
              if !(tR.contains q && !o.contains q && tX.contains q) then continue
              let x := n.id
              st := { st with foreign := st.foreign + 1 }
              -- agg: a common owner at every step
              let mut failSteps : List Int := []
              for i in [0:cs.toNat] do
                let l := Int.ofNat i
                let ok := X.nodes.any (fun z => z.id.id.step == l && owns x z.id && owns q z.id)
                if !ok then failSteps := l :: failSteps
              -- par: a parent of x linked both ways that owns q (and the same for q)
              let parOk (a b : PathNodeId) : Bool :=
                a.parent_id.isNone || (match nodesX.get? a with
                  | some na => na.parents.any (fun c => owns a c && owns c a && owns c b)
                  | none => false)
              let sonOk (a b : PathNodeId) : Bool :=
                a.id.step == cs - 1 || (match nodesX.get? a with
                  | some na => na.sons.any (fun c => owns a c && owns c a && owns c b)
                  | none => false)
              let parF := !(parOk x q && parOk q x)
              let sonF := !(sonOk x q && sonOk q x)
              if !failSteps.isEmpty then
                st := { st with aggFails := st.aggFails + 1 }
                if failSteps.any (· < r.step) then st := { st with aggBelowPin := st.aggBelowPin + 1 }
                if failSteps.any (· == r.step) then st := { st with aggAtPin := st.aggAtPin + 1 }
                if failSteps.any (· > r.step) then st := { st with aggAbovePin := st.aggAbovePin + 1 }
              if parF then st := { st with parFails := st.parFails + 1 }
              if sonF then st := { st with sonFails := st.sonFails + 1 }
              if failSteps.isEmpty && !parF && !sonF then
                st := { st with noneFails := st.noneFails + 1 }
              if st.ex.length < 6 then
                st := { st with ex := st.ex ++ [s!"pin {r.step}.{r.index} cs {cs}: {x.id.step}.{x.id.index}(par {x.parent_id.map (fun c => s!"{c.step}.{c.index}")}) -> {q.id.step}.{q.id.index}: agg fails at {failSteps.reverse}, par {parF}, son {sonF}"] }
          | _, _ => pure ()
  return st

def reportBW (name : String) (st : BWStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: foreign={st.foreign} | agg fails={st.aggFails} (below pin {st.aggBelowPin}, at pin {st.aggAtPin}, above pin {st.aggAbovePin}) | par fails={st.parFails} | son fails={st.sonFails} | NONE FAILS={st.noneFails} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


-- PinJoin (report v154): at a union by key, pinning one literal value and reviewing the union sits inside the
-- union of the pinned, reviewed sides; and if it is valid, some side is.
structure PJStat where
  joins : Nat := 0
  pins : Nat := 0
  valid : Nat := 0
  noSide : Nat := 0
  badNodes : Nat := 0
  badEntries : Nat := 0
  foreignPre : Nat := 0
  ex : List String := []

def runPinJoin (φ : Cnf) (st0 : PJStat) : PJStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some h else none
        else none)
      if sides.length < 2 then continue
      st := { st with joins := st.joins + 1 }
      let rs := ((kv.2.gowners.filter (fun q => q.id.step < lb && q.id.step ≤ Int.ofNat m)).map (·.id)).eraseDups
      for r in rs do
        st := { st with pins := st.pins + 1 }
        let X := filterAllAgg kv.2 [r]
        if !isValid X then continue
        st := { st with valid := st.valid + 1 }
        let ys := (sides.map (fun h => filterAllAgg h [r])).filter isValid
        match ys with
        | [] =>
          st := { st with noSide := st.noSide + 1 }
        | y :: rest =>
          let Z := rest.foldl doJoin y
          let tZ := ownerTable Z
          let tX := ownerTable X
          -- work the review does: entries of the union between surviving nodes that Z lacks
          for n in kv.2.nodes do
            if tX.contains n.id then
              match tZ.get? n.id with
              | none => pure ()
              | some o =>
                for q in n.owners do
                  if tX.contains q && !o.contains q then st := { st with foreignPre := st.foreignPre + 1 }
          for n in X.nodes do
            match tZ.get? n.id with
            | none => st := { st with badNodes := st.badNodes + 1 }
            | some o =>
              for q in n.owners do
                if tX.contains q && !o.contains q then
                  st := { st with badEntries := st.badEntries + 1 }
                  if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index}: {n.id.id.step}.{n.id.id.index} -> {q.id.step}.{q.id.index}"] }
  return st

def reportPJ (name : String) (st : PJStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} pins={st.pins} valid={st.valid} NO_VALID_SIDE={st.noSide} REVIEW_WORK(entries between survivors outside Z)={st.foreignPre} BAD_NODES={st.badNodes} BAD_ENTRIES={st.badEntries} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


-- The author's hint (v155): every side of a union by key has its own top node (p, p_i). At a pinned union,
-- measure the top-anchored split: cover, whether every common top owner carries the entry, and the anchored
-- triangles the support of each part needs.
structure PSStat where
  pins : Nat := 0
  entries : Nat := 0
  noCarryingAnchor : Nat := 0
  anchorNotCarrying : Nat := 0
  anchoredChecks : Nat := 0
  anchoredTriangleFails : Nat := 0
  ex : List String := []

def runPinSplit (φ : Cnf) (st0 : PSStat) : PSStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let tops : List (PathNodeId × Std.HashMap PathNodeId (Std.HashSet PathNodeId)) :=
        sides.map (fun (k, h) => ({ id := p, parent_id := some k }, ownerTable h))
      let rs := ((kv.2.gowners.filter (fun q => q.id.step < lb && q.id.step ≤ Int.ofNat m)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg kv.2 [r]
        if !isValid X then continue
        st := { st with pins := st.pins + 1 }
        let tX := ownerTable X
        let owns (a b : PathNodeId) : Bool := match tX.get? a with | some o => o.contains b | none => false
        let cs := X.current_step
        for n in X.nodes do
          for v in n.owners do
            if !tX.contains v then continue
            let x := n.id
            if x.id.step == cs - 1 || v.id.step == cs - 1 then continue
            st := { st with entries := st.entries + 1 }
            let anchors := tops.filter (fun (t, _) => tX.contains t && owns x t && owns v t)
            let carrying := anchors.filter (fun (_, tS) => match tS.get? x with | some o => o.contains v | none => false)
            if carrying.isEmpty then
              st := { st with noCarryingAnchor := st.noCarryingAnchor + 1 }
              if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"NO CARRYING ANCHOR line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index}: {x.id.step}.{x.id.index} -> {v.id.step}.{v.id.index} (anchors {anchors.length})"] }
            if carrying.length < anchors.length then
              st := { st with anchorNotCarrying := st.anchorNotCarrying + 1 }
            for (t, _) in carrying do
              for i in [0:(cs - 1).toNat] do
                let l := Int.ofNat i
                st := { st with anchoredChecks := st.anchoredChecks + 1 }
                let tS := (carrying.find? (fun (t', _) => t' == t)).map (·.2) |>.getD {}
                let carried (a b : PathNodeId) : Bool := match tS.get? a with | some o => o.contains b | none => false
                let ok := X.nodes.any (fun z => z.id.id.step == l && owns x z.id && owns v z.id && owns z.id t &&
                  carried x z.id && carried v z.id && owns z.id x && owns z.id v)
                if !ok then
                  st := { st with anchoredTriangleFails := st.anchoredTriangleFails + 1 }
                  if st.ex.length < 8 then st := { st with ex := st.ex ++ [s!"ANCHORED TRIANGLE FAILS line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index}: {x.id.step}.{x.id.index} -> {v.id.step}.{v.id.index} at step {l}"] }
  return st

def reportPS (name : String) (st : PSStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} entries={st.entries} NO_CARRYING_ANCHOR={st.noCarryingAnchor} anchorNotCarrying={st.anchorNotCarrying} | anchored triangle checks={st.anchoredChecks} FAILS={st.anchoredTriangleFails} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"


-- Is the union by key already a fixpoint of the review (no pin)? Count nodes and entries the review removes.
structure UFStat where
  joins : Nat := 0
  changed : Nat := 0
  removedNodes : Nat := 0
  removedEntries : Nat := 0
  foreignEntries : Nat := 0
  ex : List String := []

def runUnionFix (φ : Cnf) (st0 : UFStat) : UFStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some h else none
        else none)
      if sides.length < 2 then continue
      st := { st with joins := st.joins + 1 }
      let J := kv.2
      let R := filterAllAgg J []
      let tR := ownerTable R
      let tabs := sides.map ownerTable
      let mut rn := 0
      let mut re := 0
      let mut fe := 0
      for n in J.nodes do
        -- foreign entries: in the union, between nodes of one side, missing from that side's table
        for q in n.owners do
          if tabs.any (fun t => match t.get? n.id with
              | some o => t.contains q && !o.contains q
              | none => false) then fe := fe + 1
        match tR.get? n.id with
        | none => rn := rn + 1
        | some o => for q in n.owners do if tR.contains q && !o.contains q then re := re + 1
      st := { st with removedNodes := st.removedNodes + rn, removedEntries := st.removedEntries + re,
                      foreignEntries := st.foreignEntries + fe }
      if rn + re > 0 then
        st := { st with changed := st.changed + 1 }
        if st.ex.length < 6 then st := { st with ex := st.ex ++ [s!"line {m+1} key {p.step}.{p.index}: removed nodes {rn} entries {re}"] }
  return st

def reportUF (name : String) (st : UFStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} REVIEW_CHANGES_UNION={st.changed} removedNodes={st.removedNodes} removedEntries={st.removedEntries} | foreign entries in union (x,v in a side, entry not in it)={st.foreignEntries} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- Split triangles (v161, with the author's permission): in a union by key, three nodes x, v, r that are
-- pairwise owners, but no single side of the union holds all three pairs. What does the pin of r do to x→v?
structure STStat where
  joins : Nat := 0
  tri : Nat := 0
  split : Nat := 0
  splitSurvive : Nat := 0
  splitSurviveNoSide : Nat := 0
  killedDirect : Nat := 0
  killedDirectClause : Nat := 0
  killedCascade : Nat := 0
  ex : List String := []

def litS (l : Lit) : String := (if l.pos then "" else "¬") ++ s!"x{l.v}"
def cnfS (φ : Cnf) : String :=
  s!"nVars={φ.nVars} " ++ String.intercalate " ∧ " (φ.clauses.map (fun c => s!"({litS c.l1} ∨ {litS c.l2} ∨ {litS c.l3})"))
def pidS (p : PathNodeId) : String :=
  s!"{p.id.step}.{p.id.index}" ++ (match p.parent_id with | some q => s!"<{q.step}.{q.index}" | none => "")

def runSplitTri (φ : Cnf) (st0 : STStat) : STStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      st := { st with joins := st.joins + 1 }
      let J := kv.2
      let tJ := ownerTable J
      let owns (t : Std.HashMap PathNodeId (Std.HashSet PathNodeId)) (a b : PathNodeId) : Bool :=
        match t.get? a with | some o => o.contains b | none => false
      let tabs := sides.map (fun (k, h) => (k, h, ownerTable h))
      let rs := (J.gowners.filter (fun q => q.id.step < lb)).eraseDups
      for r in rs do
        let xs := J.nodes.filter (fun n => n.id != r && owns tJ n.id r)
        let mut X? : Option (Std.HashMap PathNodeId (Std.HashSet PathNodeId)) := none
        for nx in xs do
          for nv in xs do
            let x := nx.id
            let v := nv.id
            if x == v || !owns tJ x v then continue
            st := { st with tri := st.tri + 1 }
            let inOne := tabs.any (fun (_, _, t) => owns t x v && owns t x r && owns t v r)
            if inOne then continue
            st := { st with split := st.split + 1 }
            let tX ← match X? with
              | some t => pure t
              | none => do
                let X := filterAllAgg J [r.id]
                let t := if isValid X then ownerTable X else {}
                X? := some t
                pure t
            let surv := owns tX x v
            let pairs := tabs.map (fun (k, _, t) =>
              s!"side {k.step}.{k.index}: x→v {owns t x v} x→r {owns t x r} v→r {owns t v r}")
            if surv then
              st := { st with splitSurvive := st.splitSurvive + 1 }
              let kept := tabs.any (fun (_, h, _) =>
                let Y := filterAllAgg h [r.id]
                isValid Y && owns (ownerTable Y) x v)
              if !kept then st := { st with splitSurviveNoSide := st.splitSurviveNoSide + 1 }
            else
              -- killed: is there a step where every common owner of x and v already excludes the pin?
              let ox := (J.node? x).map (·.owners) |>.getD []
              let ov := (J.node? v).map (·.owners) |>.getD []
              let direct := (List.range J.current_step.toNat).filter (fun i =>
                let k := Int.ofNat i
                let com := (ownersAt ox k).filter (fun q => ov.contains q)
                !com.isEmpty && com.all (fun z => match J.node? z with
                  | some nz => !(ownersAt nz.owners r.id.step).any (fun q => q.id == r.id)
                  | none => true))
              if direct.isEmpty then st := { st with killedCascade := st.killedCascade + 1 }
              else
                st := { st with killedDirect := st.killedDirect + 1 }
                if direct.any (fun i => (Int.ofNat i) > lb) then
                  st := { st with killedDirectClause := st.killedDirectClause + 1 }
            if surv && st.ex.length < 2 then
              st := { st with ex := st.ex ++ [s!"{cnfS φ}\n    line {m+1} key {p.step}.{p.index} x={pidS x} v={pidS v} r={pidS r} | after pin r: x→v {surv}\n    " ++ String.intercalate "\n    " pairs] }
  return st

def reportST (name : String) (st : STStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: joins={st.joins} triangles={st.tri} SPLIT={st.split} splitSurvivePin={st.splitSurvive} survivesNoSide={st.splitSurviveNoSide} | killed: direct={st.killedDirect} (at a clause row {st.killedDirectClause}) cascade={st.killedCascade} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- Detailed trace of one split triangle: owners of x and v, step by step, in the union, after the pin
-- alone, after the base review and after the aggressive review.
def splitTrace (φ : Cnf) (lineIdx : Nat) (key : NodeId) (x v : PathNodeId) (r : NodeId) : List String := Id.run do
  let lines := (aggLines φ).toArray
  let some kv := lines[lineIdx]!.find? (fun e => e.1 == key) | return ["no key"]
  let J := kv.2
  let P := filterRequire J r
  let B := review P
  let X := filterAllAgg J [r]
  let mut out : List String := [cnfS φ, s!"key {key.step}.{key.index}: x={pidS x} v={pidS v} pin {r.step}.{r.index}"]
  let ownersOf' (g : GPathM) (a : PathNodeId) : List PathNodeId := match g.node? a with | some n => n.owners | none => []
  for (nm, g) in [("union", J), ("pin only", P), ("pin+review", B), ("pin+aggressive", X)] do
    let ox := ownersOf' g x
    let ov := ownersOf' g v
    out := out ++ [s!"  [{nm}] x alive {(g.node? x).isSome} v alive {(g.node? v).isSome} x→v {ox.contains v} gowners at pin step {((g.gowners.filter (fun q => q.id.step == r.step)).map pidS)}"]
    for i in [0:(J.current_step).toNat] do
      let k := Int.ofNat i
      let a := (ownersAt ox k)
      let b := (ownersAt ov k)
      let common := a.filter (fun q => b.contains q)
      if common.isEmpty || nm == "union" || nm == "pin only" then
        if a.length + b.length > 0 && (common.isEmpty || nm == "union") then
          out := out ++ [s!"      step {k}: x→{a.map pidS}  v→{b.map pidS}  common {common.map pidS}"]
  return out

-- Directed trace of a surviving split entry: per step, the common nodes of x and v that own a node of the
-- pinned map node, and which side gives each pair; then the sides after the pin.
def survTrace (φ : Cnf) (lineIdx : Nat) (key : NodeId) (x v : PathNodeId) (r : NodeId) : List String := Id.run do
  let lines := (aggLines φ).toArray
  let L := lines[lineIdx - 1]!
  let some kv := lines[lineIdx]!.find? (fun e => e.1 == key) | return ["no key"]
  let J := kv.2
  let p := key
  let sides := L.filterMap (fun e =>
    if (mapSons φ e.1.step e.1.index).contains p then
      let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
      if isValid h then some (e.1, h) else none
    else none)
  let tJ := ownerTable J
  let owns (t : Std.HashMap PathNodeId (Std.HashSet PathNodeId)) (a b : PathNodeId) : Bool :=
    match t.get? a with | some o => o.contains b | none => false
  let tabs := sides.map (fun (k, h) => (k, ownerTable h))
  let sidesOf (a b : PathNodeId) : String :=
    String.intercalate "," ((tabs.filter (fun (_, t) => owns t a b)).map (fun (k, _) => s!"{k.step}.{k.index}"))
  let rnodes := J.nodes.filter (fun n => n.id.id == r) |>.map (·.id)
  let mut out : List String := [cnfS φ, s!"key {key.step}.{key.index}  x={pidS x} v={pidS v} pin {r.step}.{r.index}  r-nodes in union: {rnodes.map pidS}",
    s!"  x→v from sides [{sidesOf x v}]"]
  for ρ in rnodes do
    out := out ++ [s!"  {pidS ρ}: x→ρ [{sidesOf x ρ}]  v→ρ [{sidesOf v ρ}]"]
  for i in [0:J.current_step.toNat] do
    let l := Int.ofNat i
    let zs := J.nodes.filter (fun n => n.id.id.step == l && owns tJ x n.id && owns tJ v n.id &&
      rnodes.any (fun ρ => owns tJ n.id ρ)) |>.map (·.id)
    let desc := zs.map (fun z => s!"{pidS z}(x:[{sidesOf x z}] v:[{sidesOf v z}] ρ:" ++
      String.intercalate "|" ((rnodes.filter (fun ρ => owns tJ z ρ)).map (fun ρ => s!"{pidS ρ}[{sidesOf z ρ}]")) ++ ")")
    out := out ++ [s!"  step {l}: " ++ String.intercalate "  " desc]
  let tX := ownerTable (filterAllAgg J [r])
  for (k, h) in sides do
    let Y := filterAllAgg h [r]
    let keep := isValid Y && owns (ownerTable Y) x v
    let t : PathNodeId := { id := p, parent_id := some k }
    out := out ++ [s!"  side {k.step}.{k.index}: pinned send valid {isValid Y}, keeps x→v {keep} | in the pinned union its top {pidS t}: alive {tX.contains t}, x→top {owns tX x t}, v→top {owns tX v t}"]
  return out

-- TopKeep (v163): in a pinned union, every side whose top both ends own keeps the entry in its pinned send.
structure TKStat where
  pins : Nat := 0
  entries : Nat := 0
  topChecks : Nat := 0
  topFails : Nat := 0
  foreignRel : Nat := 0
  noSide : Nat := 0
  noTopSide : Nat := 0
  ex : List String := []

def runTopKeep (φ : Cnf) (st0 : TKStat) : TKStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let owns (t : Std.HashMap PathNodeId (Std.HashSet PathNodeId)) (a b : PathNodeId) : Bool :=
        match t.get? a with | some o => o.contains b | none => false
      let rs := ((kv.2.gowners.filter (fun q => q.id.step < lb && q.id.step ≤ Int.ofNat m)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg kv.2 [r]
        if !isValid X then continue
        st := { st with pins := st.pins + 1 }
        let tX := ownerTable X
        let ys := sides.map (fun (k, h) =>
          let Y := filterAllAgg h [r]
          (k, ownerTable h, if isValid Y then some (ownerTable Y) else none))
        for n in X.nodes do
          for v in n.owners do
            if !tX.contains v then continue
            let x := n.id
            st := { st with entries := st.entries + 1 }
            let mut any := false
            let mut anyTop := false
            for (k, tS, tY?) in ys do
              let t : PathNodeId := { id := p, parent_id := some k }
              let keeps := match tY? with | some tY => owns tY x v | none => false
              if keeps then any := true
              if owns tX x t && owns tX v t && owns tS x v then anyTop := true
              if owns tX x t && owns tX v t then
                st := { st with topChecks := st.topChecks + 1 }
                if !keeps then
                  st := { st with topFails := st.topFails + 1 }
                  if !owns tS x v then st := { st with foreignRel := st.foreignRel + 1 }
                  if st.ex.length < 4 && owns tS x v then
                    st := { st with ex := st.ex ++ [s!"{cnfS φ}\n    line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index} side {k.step}.{k.index}: x={pidS x} v={pidS v} | entry in the side before pin {owns tS x v}"] }
            if !any then st := { st with noSide := st.noSide + 1 }
            if !anyTop then st := { st with noTopSide := st.noTopSide + 1 }
  return st

def reportTK (name : String) (st : TKStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: pins={st.pins} entries={st.entries} topChecks={st.topChecks} TOP_FAILS={st.topFails} (entry not in that side before the pin {st.foreignRel}) NO_SIDE={st.noSide} NO_TOP_SIDE_WITH_ENTRY={st.noTopSide} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- Rule 1 (v163+ chat): at a review fixpoint, do three mutual owners always share a node at every step?
structure R1Stat where
  states : Nat := 0
  triples : Nat := 0
  fails : Nat := 0
  statesWithFail : Nat := 0
  ex : List String := []

def rule1Check (X : GPathM) (st0 : R1Stat) (tag : String) : R1Stat := Id.run do
  let mut st := { st0 with states := st0.states + 1 }
  let t := ownerTable X
  let owns (a b : PathNodeId) : Bool := match t.get? a with | some o => o.contains b | none => false
  let ids := X.nodes.map (·.id)
  let mut bad := false
  for x in ids do
    for v in ids do
      if !(x.id.step < v.id.step && owns x v && owns v x) then continue
      for w in ids do
        if !(v.id.step < w.id.step && owns x w && owns w x && owns v w && owns w v) then continue
        st := { st with triples := st.triples + 1 }
        for i in [0:X.current_step.toNat] do
          let l := Int.ofNat i
          let ok := ids.any (fun z => z.id.step == l && owns x z && owns v z && owns w z)
          if !ok then
            st := { st with fails := st.fails + 1 }
            bad := true
            if st.ex.length < 4 then
              st := { st with ex := st.ex ++ [s!"{tag}: x={pidS x} v={pidS v} w={pidS w} no common node at step {l}"] }
            break
  if bad then st := { st with statesWithFail := st.statesWithFail + 1 }
  return st

def runRule1 (φ : Cnf) (st0 : R1Stat) : R1Stat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size] do
    for kv in lines[m]! do
      let R := filterAllAgg kv.2 []
      if isValid R then st := rule1Check R st s!"{cnfS φ} line {m} key {kv.1.step}.{kv.1.index}"
      let rs := ((kv.2.gowners.filter (fun q => q.id.step < lb && q.id.step < Int.ofNat m)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg kv.2 [r]
        if isValid X then st := rule1Check X st s!"{cnfS φ} line {m} key {kv.1.step}.{kv.1.index} pin {r.step}.{r.index}"
  return st

-- Common nodes of x and v at one step of a union, with their owners at the pinned step.
def commonAt (φ : Cnf) (lineIdx : Nat) (key : NodeId) (x v : PathNodeId) (rstep l : Int) : List String := Id.run do
  let lines := (aggLines φ).toArray
  let some kv := lines[lineIdx]!.find? (fun e => e.1 == key) | return ["no key"]
  let J := kv.2
  let t := ownerTable J
  let owns (a b : PathNodeId) : Bool := match t.get? a with | some o => o.contains b | none => false
  let mut out : List String := []
  for n in J.nodes do
    if n.id.id.step == l then
      let z := n.id
      let cx := owns x z && owns z x
      let cv := owns v z && owns z v
      let atR := (ownersAt n.owners rstep).map pidS
      out := out ++ [s!"  {pidS z}: x~z {cx} v~z {cv} | owners at step {rstep}: {atR}"]
  return out

-- OwnSupport (route C): in a valid pinned union, is what the union keeps of some side (nodes owning its
-- live top, pairs the side itself carries) a support of that side's send?
structure OSStat where
  pins : Nat := 0
  validX : Nat := 0
  someSide : Nat := 0
  noSide : Nat := 0
  validSideExists : Nat := 0
  sidesTried : Nat := 0
  fails : List (String × Nat) := []
  ex : List String := []

def bumpS (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map (fun e => if e.1 == k then (e.1, e.2 + 1) else e) else l ++ [(k, 1)]

def supCheck (X h : GPathM) (t : PathNodeId) : List String := Id.run do
  let tX := ownerTable X
  let memX : Std.HashSet PathNodeId := Std.HashSet.ofList (X.nodes.map (·.id))
  let relX (a b : PathNodeId) : Bool := memX.contains b && (match tX.get? a with | some o => o.contains b | none => false)
  let tH := ownerTable h
  let memH : Std.HashSet PathNodeId := Std.HashSet.ofList (h.nodes.map (·.id))
  let relH (a b : PathNodeId) : Bool := memH.contains b && (match tH.get? a with | some o => o.contains b | none => false)
  let S := (X.nodes.map (·.id)).filter (fun a => relX a t)
  let inS : Std.HashSet PathNodeId := Std.HashSet.ofList S
  let R (a b : PathNodeId) : Bool := inS.contains a && inS.contains b && relX a b && relH a b
  let cs := h.current_step
  let gow : Std.HashSet PathNodeId := Std.HashSet.ofList h.gowners
  -- neighbours by step
  let nb : Std.HashMap PathNodeId (List PathNodeId) :=
    S.foldl (fun acc a => acc.insert a (S.filter (fun b => R a b))) {}
  let nbs (a : PathNodeId) : List PathNodeId := nb.getD a []
  let mut fails : List String := []
  for a in S do
    if !gow.contains a then fails := fails ++ ["gow"]
    if !memH.contains a then fails := fails ++ ["node"]
    for i in [0:cs.toNat] do
      let l := Int.ofNat i
      if !(nbs a).any (fun v => v.id.step == l) then fails := fails ++ ["cov"]
    for b in nbs a do
      if !R b a then fails := fails ++ ["sym"]
      let nbb := nbs b
      for i in [0:cs.toNat] do
        let l := Int.ofNat i
        if !(nbs a).any (fun z => z.id.step == l && nbb.contains z) then fails := fails ++ ["agg"]
      -- parent rule
      match h.node? a with
      | none => pure ()
      | some d =>
        if a.parent_id.isSome then
          if !d.parents.any (fun c => R a c && R c a && R c b) then fails := fails ++ ["par"]
        if a.id.step != cs - 1 then
          if !h.nodes.any (fun mm => mm.parents.contains a && R a mm.id && R mm.id a && R mm.id b) then
            fails := fails ++ ["son"]
        if b.id.step + 1 == a.id.step && R b a then
          if !d.parents.contains b then fails := fails ++ ["link"]
  return fails.eraseDups

def runOwnSupport (φ : Cnf) (st0 : OSStat) : OSStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let J := kv.2
      let rs := ((J.gowners.filter (fun q => q.id.step < lb)).map (·.id)).eraseDups
      for r in rs do
        st := { st with pins := st.pins + 1 }
        let X := filterAllAgg J [r]
        if !isValid X then continue
        st := { st with validX := st.validX + 1 }
        if sides.any (fun (_, h) => isValid (filterAllAgg h [r])) then
          st := { st with validSideExists := st.validSideExists + 1 }
        let tX := ownerTable X
        let mut ok := false
        for (k, h) in sides do
          let t : PathNodeId := { id := p, parent_id := some k }
          let alive := match tX.get? t with | some o => o.contains t | none => false
          if !alive then continue
          st := { st with sidesTried := st.sidesTried + 1 }
          let f := supCheck X h t
          if f.isEmpty then ok := true
          else
            for x in f do st := { st with fails := bumpS st.fails x }
            if st.ex.length < 4 then
              st := { st with ex := st.ex ++ [s!"{cnfS φ} line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index} side {k.step}.{k.index}: fails {f}"] }
        if ok then st := { st with someSide := st.someSide + 1 }
        else st := { st with noSide := st.noSide + 1 }
  return st

-- Chain side (v165 chat): in a valid pinned union, is every live pair (a, z) held by a chain of sons,
-- each related to z, up to the top of a side whose own table carries (a, z)?
structure CSStat where
  unions : Nat := 0
  pairs : Nat := 0
  noChain : Nat := 0
  chainNoCarry : Nat := 0
  carryPinned : Nat := 0
  someTopNoCarry : Nat := 0
  ex : List String := []

def runChainSide (φ : Cnf) (st0 : CSStat) : CSStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let J := kv.2
      let rs := ((J.gowners.filter (fun q => q.id.step < lb)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg J [r]
        if !isValid X then continue
        st := { st with unions := st.unions + 1 }
        let tX := ownerTable X
        let memX : Std.HashSet PathNodeId := Std.HashSet.ofList (X.nodes.map (·.id))
        let rel (a b : PathNodeId) : Bool := memX.contains b && (match tX.get? a with | some o => o.contains b | none => false)
        let top := X.current_step - 1
        -- sons in X
        let sonsOf : Std.HashMap PathNodeId (List PathNodeId) :=
          X.nodes.foldl (fun acc n => n.parents.foldl (fun acc c => acc.insert c ((acc.getD c []) ++ [n.id])) acc) {}
        let sideTabs := sides.map (fun (k, h) => (({ id := p, parent_id := some k } : PathNodeId), ownerTable h,
          let Y := filterAllAgg h [r]; if isValid Y then some (ownerTable Y) else none))
        let ids := X.nodes.map (·.id)
        -- nodes by step, descending
        let steps := (List.range X.current_step.toNat).reverse.map Int.ofNat
        for z in ids do
          -- reach: tops reachable from each node by chains of sons related to z (and both ways to the previous)
          let mut reach : Std.HashMap PathNodeId (List PathNodeId) := {}
          for l in steps do
            for c in ids.filter (fun c => c.id.step == l) do
              if !rel c z then continue
              if l == top then reach := reach.insert c [c]
              else
                let mut acc : List PathNodeId := []
                for s' in sonsOf.getD c [] do
                  if rel c s' && rel s' c && rel s' z then
                    for t in reach.getD s' [] do
                      if !acc.contains t then acc := acc ++ [t]
                reach := reach.insert c acc
          for a in ids do
            if a == z || !rel a z then continue
            st := { st with pairs := st.pairs + 1 }
            let tops := reach.getD a []
            if tops.isEmpty then
              st := { st with noChain := st.noChain + 1 }
              continue
            let carrying := sideTabs.filter (fun (t, tS, _) => tops.contains t &&
              (match tS.get? a with | some o => o.contains z | none => false))
            if carrying.length < tops.length then
              st := { st with someTopNoCarry := st.someTopNoCarry + 1 }
            if carrying.isEmpty then
              st := { st with chainNoCarry := st.chainNoCarry + 1 }
              if st.ex.length < 4 then
                st := { st with ex := st.ex ++ [s!"{cnfS φ} line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index}: {pidS a} -> {pidS z} chain tops {tops.map pidS}"] }
            else if carrying.any (fun (_, _, tY?) => match tY? with
                | some tY => (match tY.get? a with | some o => o.contains z | none => false)
                | none => false) then
              st := { st with carryPinned := st.carryPinned + 1 }
  return st

-- Refinement: chains whose nodes are all common owners of a and z. Does every such chain reach a
-- carrying side?
structure CS2Stat where
  pairs : Nat := 0
  noChain : Nat := 0
  noCarry : Nat := 0
  someTopNoCarry : Nat := 0

def runChainSide2 (φ : Cnf) (st0 : CS2Stat) : CS2Stat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let J := kv.2
      let rs := ((J.gowners.filter (fun q => q.id.step < lb)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg J [r]
        if !isValid X then continue
        let tX := ownerTable X
        let memX : Std.HashSet PathNodeId := Std.HashSet.ofList (X.nodes.map (·.id))
        let rel (a b : PathNodeId) : Bool := memX.contains b && (match tX.get? a with | some o => o.contains b | none => false)
        let top := X.current_step - 1
        let sonsOf : Std.HashMap PathNodeId (List PathNodeId) :=
          X.nodes.foldl (fun acc n => n.parents.foldl (fun acc c => acc.insert c ((acc.getD c []) ++ [n.id])) acc) {}
        let sideTabs := sides.map (fun (k, h) => (({ id := p, parent_id := some k } : PathNodeId), ownerTable h))
        let ids := X.nodes.map (·.id)
        let steps := (List.range X.current_step.toNat).reverse.map Int.ofNat
        for a in ids do
          for z in ids do
            if a == z || !rel a z then continue
            st := { st with pairs := st.pairs + 1 }
            let mut reach : Std.HashMap PathNodeId (List PathNodeId) := {}
            for l in steps do
              if l < a.id.step then break
              for c in ids.filter (fun c => c.id.step == l) do
                if !(rel c z && (c == a || rel c a)) then continue
                if l == top then reach := reach.insert c [c]
                else
                  let mut acc : List PathNodeId := []
                  for s' in sonsOf.getD c [] do
                    if rel c s' && rel s' c && rel s' z && rel s' a then
                      for t in reach.getD s' [] do
                        if !acc.contains t then acc := acc ++ [t]
                  reach := reach.insert c acc
            let tops := reach.getD a []
            if tops.isEmpty then st := { st with noChain := st.noChain + 1 }; continue
            let carrying := sideTabs.filter (fun (t, tS) => tops.contains t &&
              (match tS.get? a with | some o => o.contains z | none => false))
            if carrying.isEmpty then st := { st with noCarry := st.noCarry + 1 }
            if carrying.length < tops.length then st := { st with someTopNoCarry := st.someTopNoCarry + 1 }
  return st

-- History invariant: follow a live pair's chain of common owners; at each line, is the pair in the table
-- of the state whose key the chain names?
structure HYStat where
  pairs : Nat := 0
  noChain : Nat := 0
  noState : Nat := 0
  levels : Nat := 0
  levelFails : Nat := 0
  pairFails : Nat := 0
  ex : List String := []

def runHistory (φ : Cnf) (st0 : HYStat) : HYStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let J := kv.2
      let rs := ((J.gowners.filter (fun q => q.id.step < lb)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg J [r]
        if !isValid X then continue
        let tX := ownerTable X
        let memX : Std.HashSet PathNodeId := Std.HashSet.ofList (X.nodes.map (·.id))
        let rel (a b : PathNodeId) : Bool := memX.contains b && (match tX.get? a with | some o => o.contains b | none => false)
        let top := X.current_step - 1
        let sonsOf : Std.HashMap PathNodeId (List PathNodeId) :=
          X.nodes.foldl (fun acc n => n.parents.foldl (fun acc c => acc.insert c ((acc.getD c []) ++ [n.id])) acc) {}
        let ids := X.nodes.map (·.id)
        let steps := (List.range X.current_step.toNat).reverse.map Int.ofNat
        for a in ids do
          for z in ids do
            if a == z || !rel a z then continue
            st := { st with pairs := st.pairs + 1 }
            -- reachability of the top through common owners of a and z
            let mut reach : Std.HashMap PathNodeId Bool := {}
            for l in steps do
              if l < a.id.step then break
              for c in ids.filter (fun c => c.id.step == l) do
                if !(rel c z && (c == a || rel c a)) then continue
                if l == top then reach := reach.insert c true
                else
                  let ok := (sonsOf.getD c []).any (fun s' =>
                    reach.getD s' false && rel c s' && rel s' c && rel s' z && rel s' a)
                  reach := reach.insert c ok
            if !(reach.getD a false) then
              st := { st with noChain := st.noChain + 1 }
              continue
            -- one such chain, greedily
            let mut chain : List PathNodeId := [a]
            let mut cur := a
            while cur.id.step < top do
              match (sonsOf.getD cur []).find? (fun s' =>
                  reach.getD s' false && rel cur s' && rel s' cur && rel s' z && rel s' a) with
              | none => cur := { cur with id := { cur.id with step := top } }  -- unreachable
              | some s' => chain := chain ++ [s']; cur := s'
            -- the invariant, line by line
            let lo := max a.id.step z.id.step
            let mut bad := false
            for c in chain do
              let l := c.id.step
              if l < lo then continue
              match lines[l.toNat]!.find? (fun e => e.1 == c.id) with
              | none => st := { st with noState := st.noState + 1 }
              | some st' =>
                st := { st with levels := st.levels + 1 }
                let t := ownerTable st'.2
                let has := match t.get? a with | some o => o.contains z | none => false
                if !has then
                  bad := true
                  st := { st with levelFails := st.levelFails + 1 }
                  if st.ex.length < 4 then
                    st := { st with ex := st.ex ++ [s!"{cnfS φ} line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index}: pair {pidS a} -> {pidS z} not in the table of line {l} key {c.id.step}.{c.id.index}"] }
            if bad then st := { st with pairFails := st.pairFails + 1 }
  return st

-- The author's triangle filter inside a family: going down step by step, do the nodes common to
-- everything picked so far ever run out?
structure TFStat where
  unions : Nat := 0
  fams : Nat := 0
  steps : Nat := 0
  fails : Nat := 0
  famFails : Nat := 0
  ex : List String := []

open AbsSat.GraphPath.Model.ImprovesCima in
def runTriFam (φ : Cnf) (st0 : TFStat) : TFStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := sidesOf φ L p
      if sides.length < 2 then continue
      let J := kv.2
      let rs := (((J.gowners.filter (fun q => q.id.step < lb)).map (·.id)).eraseDups).take 3
      for r in ([] :: rs.map (fun r => [r])) do
        let X := filterAllAgg J r
        if !isValid X then continue
        st := { st with unions := st.unions + 1 }
        for t in ((X.line (X.current_step - 1)).map (·.id)) do
          let F := famFix sides t X
          if !isValid F then continue
          st := { st with fams := st.fams + 1 }
          -- the descent, with fast tables
          let tF := ownerTable F
          let rel (a b : PathNodeId) : Bool :=
            match tF.get? a with | some o => o.contains b | none => false
          let mut byStep : Std.HashMap Int (List PathNodeId) := {}
          for n in F.nodes do
            byStep := byStep.insert n.id.id.step ((byStep.getD n.id.id.step []) ++ [n.id])
          let mut picks : List PathNodeId := []
          let mut bad := false
          for n in [0:F.current_step.toNat] do
            let l := F.current_step - 1 - (n : Int)
            st := { st with steps := st.steps + 1 }
            let cand := (byStep.getD l []).filter (fun z => picks.all (fun y => rel z y && rel y z))
            match cand with
            | [] =>
              bad := true
              st := { st with fails := st.fails + 1 }
              if st.ex.length < 4 then
                st := { st with ex := st.ex ++
                  [s!"{cnfS φ} line {m+1} key {p.step}.{p.index} top {pidS t} step {l} after {picks.length} picks"] }
              break
            | z :: _ => picks := z :: picks
          if bad then st := { st with famFails := st.famFails + 1 }
  return st

-- The author's filter AS THE LEAN DEFINITION runs it (`famTriOkB`), not a hand-rolled copy: does the
-- Bool that `sat_of_filterCheck` reads actually come back true on real unions? Run on the plain fixed
-- union, which is the harder object than the rule-filtered one the theorem speaks of.
open AbsSat.GraphPath.Model.ImprovesCima in
def runBCheck (φ : Cnf) (st0 : Nat × Nat × Nat) : Nat × Nat × Nat := Id.run do
  let mut ok := st0.1
  let mut bad := st0.2.1
  let mut uni := st0.2.2
  let lines := (aggLines φ).toArray
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := sidesOf φ L p
      if sides.length < 2 then continue
      let X := filterAllAgg kv.2 []
      if !isValid X then continue
      uni := uni + 1
      if famTriOkB sides X then ok := ok + 1 else bad := bad + 1
  return (ok, bad, uni)

-- The family indexed by chains: pairs whose chain of common owners ends at the top t, kept only when
-- the side itself carries them. Are the closure rules of a support satisfied?
structure CFStat where
  tops : Nat := 0
  pairs : Nat := 0
  covFails : Nat := 0
  aggFails : Nat := 0
  parFails : Nat := 0
  sonFails : Nat := 0
  linkFails : Nat := 0
  ex : List String := []

def runChainFam (φ : Cnf) (st0 : CFStat) : CFStat := Id.run do
  let mut st := st0
  let lines := (aggLines φ).toArray
  let lb : Int := 2 * (φ.nVars : Int)
  for m in [0:lines.size - 1] do
    let L := lines[m]!
    for kv in lines[m+1]! do
      let p := kv.1
      let sides := L.filterMap (fun e =>
        if (mapSons φ e.1.step e.1.index).contains p then
          let h := up (filterAllAgg (filterWeakAll e.2 (weakReqOfCnf φ p)) (reqOfCnf φ p)) p ""
          if isValid h then some (e.1, h) else none
        else none)
      if sides.length < 2 then continue
      let J := kv.2
      let rs := ((J.gowners.filter (fun q => q.id.step < lb)).map (·.id)).eraseDups
      for r in rs do
        let X := filterAllAgg J [r]
        if !isValid X then continue
        let tX := ownerTable X
        let memX : Std.HashSet PathNodeId := Std.HashSet.ofList (X.nodes.map (·.id))
        let rel (a b : PathNodeId) : Bool := memX.contains b && (match tX.get? a with | some o => o.contains b | none => false)
        let topStep := X.current_step - 1
        let sonsOf : Std.HashMap PathNodeId (List PathNodeId) :=
          X.nodes.foldl (fun acc n => n.parents.foldl (fun acc c => acc.insert c ((acc.getD c []) ++ [n.id])) acc) {}
        let ids := X.nodes.map (·.id)
        let steps := (List.range X.current_step.toNat).reverse.map Int.ofNat
        -- tops reachable by a chain of common owners of a and b
        let chainTops (a b : PathNodeId) : List PathNodeId := Id.run do
          let mut reach : Std.HashMap PathNodeId (List PathNodeId) := {}
          for l in steps do
            if l < a.id.step then break
            for c in ids.filter (fun c => c.id.step == l) do
              if !(rel c b && (c == a || rel c a)) then continue
              if l == topStep then reach := reach.insert c [c]
              else
                let mut acc : List PathNodeId := []
                for s' in sonsOf.getD c [] do
                  if rel c s' && rel s' c && rel s' b && rel s' a then
                    for t in reach.getD s' [] do
                      if !acc.contains t then acc := acc ++ [t]
                reach := reach.insert c acc
          return reach.getD a []
        for (k, h) in sides do
          let t : PathNodeId := { id := p, parent_id := some k }
          if !rel t t then continue
          st := { st with tops := st.tops + 1 }
          let tH := ownerTable h
          let memH : Std.HashSet PathNodeId := Std.HashSet.ofList (h.nodes.map (·.id))
          let relH (a b : PathNodeId) : Bool := memH.contains b && (match tH.get? a with | some o => o.contains b | none => false)
          let S := ids.filter (fun a => rel a t)
          let R (a b : PathNodeId) : Bool :=
            rel a b && relH a b && relH b a && (chainTops a b).contains t
          let cs := h.current_step
          for a in S do
            let nbs := S.filter (fun b => R a b)
            st := { st with pairs := st.pairs + nbs.length }
            for i in [0:cs.toNat] do
              let l := Int.ofNat i
              if !nbs.any (fun b => b.id.step == l) then
                st := { st with covFails := st.covFails + 1 }
                if st.ex.length < 3 then
                  st := { st with ex := st.ex ++ [s!"cov: {cnfS φ} line {m+1} key {p.step}.{p.index} pin {r.step}.{r.index} top {pidS t} node {pidS a} step {l}"] }
                break
            for b in nbs do
              let nbb := S.filter (fun z => R b z)
              for i in [0:cs.toNat] do
                let l := Int.ofNat i
                if !nbs.any (fun z => z.id.step == l && nbb.contains z) then
                  st := { st with aggFails := st.aggFails + 1 }
                  break
              match h.node? a with
              | none => pure ()
              | some d =>
                if a.parent_id.isSome && !d.parents.any (fun c => R a c && R c a && R c b) then
                  st := { st with parFails := st.parFails + 1 }
                if a.id.step != cs - 1 &&
                    !h.nodes.any (fun mm => mm.parents.contains a && R a mm.id && R mm.id a && R mm.id b) then
                  st := { st with sonFails := st.sonFails + 1 }
                if b.id.step + 1 == a.id.step && R b a && !d.parents.contains b then
                  st := { st with linkFails := st.linkFails + 1 }
  return st

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
  | "clique" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runClique φ 20000000 {})
        let t1 ← IO.monoMsNow
        reportQ s!"clique {path}" st (t1 - t0)
  | "pieces" :: "random" :: maxK :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PcStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPieces φ maxK.toNat! 8 st
      let t1 ← IO.monoMsNow
      reportPc s!"pieces seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pieces" :: maxK :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPieces φ maxK.toNat! 8 {})
        let t1 ← IO.monoMsNow
        reportPc s!"pieces {path}" st (t1 - t0)
  | "split" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : SpStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runSplit φ st
      let t1 ← IO.monoMsNow
      reportSp s!"split seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "split" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSplit φ {})
        let t1 ← IO.monoMsNow
        reportSp s!"split {path}" st (t1 - t0)
  | "restrict" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : RsStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runRestrict φ st
      let t1 ← IO.monoMsNow
      reportRs s!"restrict seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "restrict" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runRestrict φ {})
        let t1 ← IO.monoMsNow
        reportRs s!"restrict {path}" st (t1 - t0)
  | "sliceclosed" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSliceClosed φ 2000000 {})
        let t1 ← IO.monoMsNow
        reportSc s!"sliceclosed {path}" st (t1 - t0)
  | "weakcmp" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        IO.println s!"weakcmp {path}"
        runWeakCmp φ
  | "splice" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSplice φ 200000 15 {})
        let t1 ← IO.monoMsNow
        reportSplice s!"splice {path}" st (t1 - t0)
  | "greedy" :: sample :: budget :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runGreedy φ budget.toNat! sample.toNat! {})
        let t1 ← IO.monoMsNow
        reportGreedy s!"greedy {path}" st (t1 - t0)
  | "pinext" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PxStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPinExt φ 3 seed st
      let t1 ← IO.monoMsNow
      reportPx s!"pinext seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pinext" :: walks :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPinExt φ walks.toNat! 7 {})
        let t1 ← IO.monoMsNow
        reportPx s!"pinext {path}" st (t1 - t0)
  | "pinup" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PinUpStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPinUp φ 3 seed st
      let t1 ← IO.monoMsNow
      reportPinUp s!"pinup seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pinup" :: walks :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPinUp φ walks.toNat! 11 {})
        let t1 ← IO.monoMsNow
        reportPinUp s!"pinup {path}" st (t1 - t0)
  | "triplea" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : TaStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runTripleA φ 2 seed st
      let t1 ← IO.monoMsNow
      reportTa s!"triplea seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "triplea" :: walks :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runTripleA φ walks.toNat! 13 {})
        let t1 ← IO.monoMsNow
        reportTa s!"triplea {path}" st (t1 - t0)
  | "sidecls" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : SideStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runSideCls φ st
      let t1 ← IO.monoMsNow
      reportSide s!"sidecls seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "sidecls" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSideCls φ {})
        let t1 ← IO.monoMsNow
        reportSide s!"sidecls {path}" st (t1 - t0)
  | "surv" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : SrStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runSurv φ 100000 st
      let t1 ← IO.monoMsNow
      reportSurv s!"surv seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "surv" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runSurv φ 100000 {})
        let t1 ← IO.monoMsNow
        reportSurv s!"surv {path}" st (t1 - t0)
  | "noborrow" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : NbStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runNoBorrow φ 100000 st
      let t1 ← IO.monoMsNow
      reportNb s!"noborrow seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "noborrow" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runNoBorrow φ 100000 {})
        let t1 ← IO.monoMsNow
        reportNb s!"noborrow {path}" st (t1 - t0)
  | "entrypin" :: walks :: sample :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runEntryPin φ walks.toNat! sample.toNat! 17 {})
        let t1 ← IO.monoMsNow
        reportEp s!"entrypin {path}" st (t1 - t0)
  | "seqpin" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        IO.print s!"{path}: "
        runSeqPin φ
  | "answer" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => AbsSat.GraphPath.Model.Answer.answer φ)
        let t1 ← IO.monoMsNow
        let txt := match a with
          | .unsat => "UNSAT"
          | .sat asg => s!"SAT (certificate checked: {AbsSat.Cnf.satB asg φ}) {(List.range φ.nVars).map (fun v => if asg v then 1 else 0)}"
          | .unknown => "UNKNOWN"
        IO.println s!"answer {path}: {txt} | {t1 - t0}ms"
  | "adversarial" :: steps :: width :: iters :: restarts :: seeds =>
    for seed in seeds.map String.toNat! do
      runAdversarial steps.toNat! width.toNat! iters.toNat! restarts.toNat! seed
  | "ghosts" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        IO.println s!"ghosts {path}"
        runGhosts φ 200000
  | "why" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        IO.println s!"why {path}"
        runWhy φ 200000 8
  | "weakexact" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PeStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runWeakExact φ 200000 12 st
      let t1 ← IO.monoMsNow
      reportPe s!"weakexact seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "weakexact" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runWeakExact φ 200000 12 {})
        let t1 ← IO.monoMsNow
        reportPe s!"weakexact {path}" st (t1 - t0)
  | "pinexact" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PeStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPinExact φ 200000 st
      let t1 ← IO.monoMsNow
      reportPe s!"pinexact seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pinexact" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPinExact φ 200000 {})
        let t1 ← IO.monoMsNow
        reportPe s!"pinexact {path}" st (t1 - t0)
  | "helly3" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : H3Stat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runHelly3 φ 200000 st
      let t1 ← IO.monoMsNow
      reportH3 s!"helly3 seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "helly3" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runHelly3 φ 200000 {})
        let t1 ← IO.monoMsNow
        reportH3 s!"helly3 {path}" st (t1 - t0)
  | "linked" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : LkStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runLinked φ 200000 st
      let t1 ← IO.monoMsNow
      reportLk s!"linked seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "linked" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runLinked φ 200000 {})
        let t1 ← IO.monoMsNow
        reportLk s!"linked {path}" st (t1 - t0)
  | "pathcsp" :: steps :: width :: nreq :: trials :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let st ← IO.lazyPure (fun _ => runPathCsp steps.toNat! width.toNat! nreq.toNat! trials.toNat! seed)
      let t1 ← IO.monoMsNow
      reportPu s!"pathcsp steps={steps} width={width} reqs={nreq} seed={seed}" st (t1 - t0)
  | "pathunionrec" :: steps :: width :: paths :: trials :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let st ← IO.lazyPure (fun _ => runPathUnion steps.toNat! width.toNat! paths.toNat! trials.toNat! seed true)
      let t1 ← IO.monoMsNow
      reportPu s!"pathunion (recombination-closed) steps={steps} width={width} paths={paths} seed={seed}" st (t1 - t0)
  | "pathunion" :: steps :: width :: paths :: trials :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let st ← IO.lazyPure (fun _ => runPathUnion steps.toNat! width.toNat! paths.toNat! trials.toNat! seed)
      let t1 ← IO.monoMsNow
      reportPu s!"pathunion steps={steps} width={width} paths={paths} seed={seed}" st (t1 - t0)
  | "oracle" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : OStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runOracle φ 20000 st
      let t1 ← IO.monoMsNow
      reportO s!"oracle seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "oracle" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runOracle φ 20000 {})
        let t1 ← IO.monoMsNow
        reportO s!"oracle {path}" st (t1 - t0)
  | "distrib" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : DiStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runDistrib φ st
      let t1 ← IO.monoMsNow
      reportDi s!"distrib seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "distrib" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runDistrib φ {})
        let t1 ← IO.monoMsNow
        reportDi s!"distrib {path}" st (t1 - t0)
  | "nested" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : NStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runNested φ 200000 st
      let t1 ← IO.monoMsNow
      reportN s!"nested seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "nested" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runNested φ 200000 {})
        let t1 ← IO.monoMsNow
        reportN s!"nested {path}" st (t1 - t0)
  | "futures" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : FStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runFutures φ 200000 st
      let t1 ← IO.monoMsNow
      reportF s!"futures seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "futures" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runFutures φ 200000 {})
        let t1 ← IO.monoMsNow
        reportF s!"futures {path}" st (t1 - t0)
  | "cover" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : CovStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runCover φ 200000 st
      let t1 ← IO.monoMsNow
      reportCov s!"cover seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "cover" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runCover φ 200000 {})
        let t1 ← IO.monoMsNow
        reportCov s!"cover {path}" st (t1 - t0)
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
  | "unionfix" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runUnionFix φ {})
        let t1 ← IO.monoMsNow
        reportUF s!"unionfix {path}" st (t1 - t0)
  | "splittri" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : STStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runSplitTri φ st
      let t1 ← IO.monoMsNow
      reportST s!"splittri seed {seed}" st (t1 - t0)
  | "splittrace" :: seed :: idx :: line :: ks :: ki :: xs :: xi :: xps :: xpi :: vs :: vi :: vps :: vpi :: rs :: ri :: _ =>
    let φs := randomCnfs 10 3 seed.toNat!
    let some φ := φs[idx.toNat!]? | IO.println "no formula"
    let pid (s i ps pi : String) : AbsSat.Utils.Alias.PathNodeId :=
      { id := ⟨s.toInt!, i.toInt!⟩, parent_id := if ps == "-" then none else some ⟨ps.toInt!, pi.toInt!⟩ }
    for l in splitTrace φ line.toNat! ⟨ks.toInt!, ki.toInt!⟩ (pid xs xi xps xpi) (pid vs vi vps vpi) ⟨rs.toInt!, ri.toInt!⟩ do
      IO.println l
  | "survtrace" :: seed :: nvMin :: idx :: line :: ks :: ki :: xs :: xi :: xps :: xpi :: vs :: vi :: vps :: vpi :: rs :: ri :: _ =>
    let φs := randomCnfs 10 nvMin.toNat! seed.toNat!
    let some φ := φs[idx.toNat!]? | IO.println "no formula"
    let pid (s i ps pi : String) : AbsSat.Utils.Alias.PathNodeId :=
      { id := ⟨s.toInt!, i.toInt!⟩, parent_id := if ps == "-" then none else some ⟨ps.toInt!, pi.toInt!⟩ }
    for l in survTrace φ line.toNat! ⟨ks.toInt!, ki.toInt!⟩ (pid xs xi xps xpi) (pid vs vi vps vpi) ⟨rs.toInt!, ri.toInt!⟩ do
      IO.println l
  | "topkeep" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : TKStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runTopKeep φ st
      let t1 ← IO.monoMsNow
      reportTK s!"topkeep seed {seed}" st (t1 - t0)
  | "splittracef" :: path :: line :: ks :: ki :: xs :: xi :: xps :: xpi :: vs :: vi :: vps :: vpi :: rs :: ri :: _ =>
    match ← loadCnf path with
    | none => IO.println "bad cnf"
    | some φ =>
      let pid (s i ps pi : String) : AbsSat.Utils.Alias.PathNodeId :=
        { id := ⟨s.toInt!, i.toInt!⟩, parent_id := if ps == "-" then none else some ⟨ps.toInt!, pi.toInt!⟩ }
      for l in splitTrace φ line.toNat! ⟨ks.toInt!, ki.toInt!⟩ (pid xs xi xps xpi) (pid vs vi vps vpi) ⟨rs.toInt!, ri.toInt!⟩ do
        IO.println l
      IO.println "--- survtrace"
      for l in survTrace φ line.toNat! ⟨ks.toInt!, ki.toInt!⟩ (pid xs xi xps xpi) (pid vs vi vps vpi) ⟨rs.toInt!, ri.toInt!⟩ do
        IO.println l
  | "rule1" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : R1Stat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runRule1 φ st
      let t1 ← IO.monoMsNow
      IO.println s!"rule1 seed {seed}: states={st.states} triples={st.triples} FAILS={st.fails} statesWithFail={st.statesWithFail} | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "commonat" :: path :: line :: ks :: ki :: xs :: xi :: xps :: xpi :: vs :: vi :: vps :: vpi :: rs :: l :: _ =>
    match ← loadCnf path with
    | none => IO.println "bad cnf"
    | some φ =>
      let pid (s i ps pi : String) : AbsSat.Utils.Alias.PathNodeId :=
        { id := ⟨s.toInt!, i.toInt!⟩, parent_id := if ps == "-" then none else some ⟨ps.toInt!, pi.toInt!⟩ }
      for o in commonAt φ line.toNat! ⟨ks.toInt!, ki.toInt!⟩ (pid xs xi xps xpi) (pid vs vi vps vpi) rs.toInt! l.toInt! do
        IO.println o
  | "ownsupport" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : OSStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runOwnSupport φ st
      let t1 ← IO.monoMsNow
      IO.println s!"ownsupport seed {seed}: pins={st.pins} validPinnedUnion={st.validX} validSideExists={st.validSideExists} | OWN_SUPPORT some side={st.someSide} NONE={st.noSide} (sides tried {st.sidesTried}, field failures {st.fails}) | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "chainside" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : CSStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runChainSide φ st
      let t1 ← IO.monoMsNow
      IO.println s!"chainside seed {seed}: pinned unions={st.unions} live pairs={st.pairs} | NO_CHAIN={st.noChain} CHAIN_BUT_NO_SIDE_CARRIES={st.chainNoCarry} | carried also in the side's pinned send={st.carryPinned} | pairs where SOME reached top does not carry={st.someTopNoCarry} | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "chainside2" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : CS2Stat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runChainSide2 φ st
      let t1 ← IO.monoMsNow
      IO.println s!"chainside2 seed {seed}: live pairs={st.pairs} | NO_CHAIN={st.noChain} NO_SIDE_CARRIES={st.noCarry} | SOME_TOP_NOT_CARRYING={st.someTopNoCarry} | {t1 - t0}ms"
  | "history" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : HYStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runHistory φ st
      let t1 ← IO.monoMsNow
      IO.println s!"history seed {seed}: pairs={st.pairs} noChain={st.noChain} | levels checked={st.levels} LEVEL_FAILS={st.levelFails} PAIRS_WITH_A_FAIL={st.pairFails} (states not found {st.noState}) | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "trifam" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : TFStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runTriFam φ st
      let t1 ← IO.monoMsNow
      IO.println s!"trifam seed {seed}: filtered unions={st.unions} families={st.fams} steps={st.steps} | EMPTY_INTERSECTION={st.fails} families with a fail={st.famFails} | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "bcheck" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : Nat × Nat × Nat := (0, 0, 0)
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runBCheck φ st
      let t1 ← IO.monoMsNow
      IO.println s!"bcheck seed {seed}: unions={st.2.2} famTriOkB TRUE={st.1} FALSE={st.2.1} | {t1 - t0}ms"
  | "chainfam" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : CFStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runChainFam φ st
      let t1 ← IO.monoMsNow
      IO.println s!"chainfam seed {seed}: tops={st.tops} pairs={st.pairs} | COV={st.covFails} AGG={st.aggFails} PAR={st.parFails} SON={st.sonFails} LINK={st.linkFails} | {t1 - t0}ms"
      for e in st.ex do IO.println s!"  EX {e}"
  | "pinsplit" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPinSplit φ {})
        let t1 ← IO.monoMsNow
        reportPS s!"pinsplit {path}" st (t1 - t0)
  | "pinjoin" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PJStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPinJoin φ st
      let t1 ← IO.monoMsNow
      reportPJ s!"pinjoin seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "pinjoin" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPinJoin φ {})
        let t1 ← IO.monoMsNow
        reportPJ s!"pinjoin {path}" st (t1 - t0)
  | "basewhy" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runBaseWhy φ {})
        let t1 ← IO.monoMsNow
        reportBW s!"basewhy {path}" st (t1 - t0)
  | "basejoin" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runBaseJoin φ {})
        let t1 ← IO.monoMsNow
        reportBJ s!"basejoin {path}" st (t1 - t0)
  | "pin1" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPin1 φ {})
        let t1 ← IO.monoMsNow
        reportP1 s!"pin1 {path}" st (t1 - t0)
  | "pincommute" :: "random" :: depth :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : PCStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := runPinCommute φ depth.toNat! st
      let t1 ← IO.monoMsNow
      reportPC s!"pincommute seed {seed} ({cases} formulas, {nvMin}+ vars, depth {depth})" st (t1 - t0)
  | "pincommute" :: depth :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => runPinCommute φ depth.toNat! {})
        let t1 ← IO.monoMsNow
        reportPC s!"pincommute {path}" st (t1 - t0)
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
