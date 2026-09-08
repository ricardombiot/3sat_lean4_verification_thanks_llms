-- lean_project/AbsSat/GraphPath/Model/L6Search.lean
import AbsSat.GraphPath.Model.Filter

/-!
An executable falsifier for bridge lemma **L6** (`L6.lean`).

It builds machine states with `initSeed` / `upFiltering` / `join` over
synthetic maps whose requirements are arbitrary subject only to `Reachable`'s
hypotheses — strictly backward-pointing and step-distinct — with no 3SAT
structure at all, then enumerates *every* candidate selection of one node per
step and checks `IsChain ∧ PairwiseOwned` on it. A state that is `isValid` but
has no such selection is a counterexample to L6.

This is validation infrastructure, not proof material. Run it with
`lake exe l6search [steps] [width] [trials]`.
-/

namespace L6Search
open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

def selections (g : GPathM) : List (List PathNodeId) :=
  (intRange 0 (g.current_step - 1)).foldl
    (fun acc k =>
      let cands := (g.line k).map (·.id)
      acc.flatMap (fun pre => cands.map (fun c => pre ++ [c])))
    [[]]

def ownersOfB (g : GPathM) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with | some n => n.owners | none => []

def isGoodChain (g : GPathM) (sel : List PathNodeId) : Bool :=
  let idxs := List.range sel.length
  idxs.all (fun i =>
    match sel[i]? with
    | some p => (g.node? p).isSome && p.id.step == (i : Int)
    | none => false)
  && idxs.all (fun i =>
    if i + 1 < sel.length then
      match sel[i]?, sel[i+1]? with
      | some p, some q => match g.node? q with
                          | some n => n.parents.contains p
                          | none => false
      | _, _ => false
    else true)
  && idxs.all (fun i => idxs.all (fun j =>
    if i == j then true
    else match sel[i]?, sel[j]? with
      | some p, some q => (ownersOfB g q).contains p
      | _, _ => false))

def hasChain (g : GPathM) : Bool := (selections g).any (isGoodChain g)

-- ---- synthetic map: `width` nodes per step, random backward requirements ----

structure SynMap where
  steps : Nat
  width : Nat
  reqs  : NodeId → List NodeId

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Requirements: for each earlier step, with probability ~1/2 demand one
specific node of that step.  Backward and step-distinct by construction, so
every state built below satisfies `Reachable`'s hypotheses. -/
def mkReqs (width : Nat) (seed : Nat) (d : NodeId) : List NodeId :=
  (List.range d.step.toNat).filterMap (fun k =>
    let h := lcg (seed + d.step.toNat * 97 + d.index.toNat * 31 + k * 7)
    if h % 2 == 0 then none
    else some { step := (k : Int), index := ((h / 2) % width : Nat) })

abbrev Line := List (NodeId × GPathM)

def insertG (line : Line) (key : NodeId) (g : GPathM) : Line :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, ex) => line.map (fun kv => if kv.1 == key then (key, join ex g) else kv)
  | none => line ++ [(key, g)]

def advance (m : SynMap) (k : Nat) (line : Line) : Line :=
  line.foldl (fun next kv =>
    (List.range m.width).foldl (fun next (i : Nat) =>
      let dest : NodeId := { step := (k : Int), index := (i : Int) }
      let g' := upFiltering kv.2 (m.reqs dest) dest "n"
      if isValid g' then insertG next dest g' else next) next) []

def runMap (m : SynMap) : Line :=
  (List.range (m.steps - 1)).foldl (fun line k => advance m (k + 1) line)
    ((List.range m.width).foldl (fun line (i : Nat) =>
        let d : NodeId := { step := 0, index := (i : Int) }
        insertG line d (initSeed d "n")) [])

-- ============================================================
-- Probe: are the owners tables 0/1/all at the map level?
-- ============================================================

/-- Map nodes a node's owners still allow at step `j`. -/
def mapIdsAt (n : PNodeM) (j : Int) : List NodeId :=
  (n.owners.filter (fun q => q.id.step == j)).map (·.id)

/-- `true` when the projection is a single map node, or contains every map node
still available at that step — the 0/1/all shape the CCJ argument needs. -/
def allOrOneAt (g : GPathM) (n : PNodeM) (j : Int) : Bool :=
  match mapIdsAt n j with
  | [] => false                       -- empty: an arc-consistency failure, not 0/1/all
  | m :: ms =>
    ms.all (fun m' => m' == m)
      || ((g.line j).map (fun d => d.id.id)).all (fun a => (m :: ms).contains a)

/-- Nodes/steps of `g` where the 0/1/all shape fails. -/
def allOrOneViolations (g : GPathM) : Nat :=
  (g.nodes.foldl (fun acc n =>
    acc + ((intRange 0 (g.current_step - 1)).filter
      (fun j => !allOrOneAt g n j)).length) 0)

/-- Split the failures: `(empty projection, proper-subset-of-2-or-more)`. The
first is an arc-consistency failure; only the second refutes the 0/1/all
shape. -/
def allOrOneSplit (g : GPathM) : Nat × Nat :=
  g.nodes.foldl (fun acc n =>
    (intRange 0 (g.current_step - 1)).foldl (fun (a : Nat × Nat) j =>
      match mapIdsAt n j with
      | [] => (a.1 + 1, a.2)
      | m :: ms =>
        if ms.all (fun m' => m' == m)
            || ((g.line j).map (fun d => d.id.id)).all (fun x => (m :: ms).contains x)
        then a else (a.1, a.2 + 1)) acc) (0, 0)

/-- The same, but only over graphs the machine would keep (`isValid`). -/
def allOrOneSplitValid (g : GPathM) : Nat × Nat :=
  if isValid g then allOrOneSplit g else (0, 0)

/-- Every line the machine holds, not just the last: `runMap` keeps only the
final step, but a support failure at any intermediate step is just as much a
counterexample. -/
def runMapAll (m : SynMap) : List Line :=
  (List.range (m.steps - 1)).foldl
    (fun (acc : List Line) k =>
      match acc.getLast? with
      | some line => acc ++ [advance m (k + 1) line]
      | none => acc)
    [((List.range m.width).foldl (fun line (i : Nat) =>
        let d : NodeId := { step := 0, index := (i : Int) }
        insertG line d (initSeed d "n")) [])]

/-- Valid states with no complete co-owned chain, over every step. -/
def badStatesAll (m : SynMap) : Nat :=
  (runMapAll m).foldl (fun acc line =>
    acc + (line.filterMap (fun kv =>
      if isValid kv.2 && !hasChain kv.2 then some kv.2 else none)).length) 0

/-- 0/1/all violations over every state at every step. -/
def allOrOneAll (m : SynMap) : Nat × Nat :=
  (runMapAll m).foldl (fun acc line =>
    line.foldl (fun (a : Nat × Nat) kv =>
      let s := allOrOneSplitValid kv.2
      (a.1 + s.1, a.2 + s.2)) acc) (0, 0)

/-- Total states inspected by `badStatesAll`. -/
def statesAll (m : SynMap) : Nat :=
  (runMapAll m).foldl (fun acc line => acc + line.length) 0

/-- A witness of L6 failing: valid but with no complete co-owned chain. -/
def badStates (m : SynMap) : List GPathM :=
  (runMap m).filterMap (fun kv => if isValid kv.2 && !hasChain kv.2 then some kv.2 else none)

def search (steps width trials : Nat) : Nat × Nat :=
  (List.range trials).foldl (fun (acc : Nat × Nat) t =>
    let m : SynMap := { steps := steps, width := width, reqs := mkReqs width (t * 7919 + 1) }
    let bad := (badStates m).length
    (acc.1 + 1, acc.2 + bad)) (0, 0)

end L6Search

open L6Search

namespace L6Search
open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
/-- Diagnostics: (maps, final states, valid states, states with a branching
line, total selections explored, L6 failures). -/
def diag (steps width trials : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (List.range trials).foldl (fun acc t =>
    let m : SynMap := { steps := steps, width := width, reqs := mkReqs width (t * 7919 + 1) }
    let line := runMap m
    let states := line.map (·.2)
    let valid := states.filter (fun g => isValid g)
    let branching := valid.filter (fun g =>
      (intRange 0 (g.current_step - 1)).any (fun k => (g.line k).length > 1))
    let sels := valid.foldl (fun s g => s + (selections g).length) 0
    let bad := (badStates m).length
    (acc.1 + 1, acc.2.1 + states.length, acc.2.2.1 + valid.length,
     acc.2.2.2.1 + branching.length, acc.2.2.2.2.1 + sels, acc.2.2.2.2.2 + bad))
    (0, 0, 0, 0, 0, 0)
end L6Search


namespace L6Search
open AbsSat.Utils.Alias AbsSat.GraphPath.Model AbsSat.GraphPath.Model.GPathM
/-- (maps, valid states, richest state's selection count, states with ≥8
selections, total selections, L6 failures) -/
def diag2 (steps width trials : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (List.range trials).foldl (fun acc t =>
    let m : SynMap := { steps := steps, width := width, reqs := mkReqs width (t * 7919 + 1) }
    let states := (runMap m).map (·.2)
    let sels := states.map (fun g => (selections g).length)
    let mx := sels.foldl Nat.max 0
    let rich := (sels.filter (· ≥ 8)).length
    let bad := badStatesAll m
    (acc.1 + statesAll m, Nat.max acc.2.1 mx, acc.2.2.1 + rich,
     acc.2.2.2.1 + (allOrOneAll m).1 * 1000 + (allOrOneAll m).2, acc.2.2.2.2 + bad))
    (0, 0, 0, 0, 0)
end L6Search

