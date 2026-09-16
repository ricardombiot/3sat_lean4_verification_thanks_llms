import AbsSat.SatMachine.PureSatMachine
import AbsSat.Cnf.Dimacs
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.SatMachine.DiffTest

/-! # Does a join borrow facts across its sides?

Measures the obligation `JoinDescent.SideCovered`, the residue of `JoinCovered` left by
`joinCovered_of_sideCovered`.

At every join the driver performs, `chain_on_one_side` says a partial chain of `join g₁ g₂`
has **all** its picks in `g₁` or all in `g₂`. What is not proved is what happens next: such a
chain need not be a chain of *that* side, because `mergeNode` unions owners, parents and sons,
so the chain may rest on an owner entry, a link or a global owner that only the **other** side
supplies. Call such a chain *borrowed*. `SideCovered` says every borrowed chain still extends
one step down.

This probe reimplements the driver's advance (`insertPure` / `sendTo` / `sendAll` /
`pureAdvance`) so it can keep both operands of every join, then for each join:

* enumerates the partial chains of the join (steps `lo .. hi`, `0 < lo ≤ hi < current_step`);
* checks the dichotomy (a violation would contradict `chain_on_one_side` — expected 0);
* for each side that contains all the picks, reports whether the chain is already a chain of
  that side or is **borrowed**, and which condition fails when borrowed;
* for every borrowed chain, whether it extends to `lo - 1` — the `SideCovered` verdict.

Usage: `lake exe join-borrow file <cnf>...`
-/

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver

namespace Probes.JoinBorrow

-- ============================================================
-- Views
-- ============================================================

def ownersL (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.owners | none => []

def parentsL (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.parents | none => []

def sonsL (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.sons | none => []

def showP (p : PathNodeId) : String :=
  s!"({p.id.step},{p.id.index},{p.parent_id.map (·.index)})"

-- ============================================================
-- The `SoundOn` conditions, as Bool
-- ============================================================

/-- The single-pick conditions: `node`, `gowner`, `self_owned`, `root_shape`. -/
def pickOk (G : GPathM) (p : PathNodeId) (k : Int) : Bool :=
  (G.node? p).isSome && p.id.step == k && G.gowners.contains p
    && (ownersL G p).contains p
    && (if k == 0 then p.parent_id.isNone else p.parent_id.isSome)

/-- `c` may be prepended below `low` as the new lowest pick of `seg`: linked both ways, and
mutually owned with every pick already there (`owned` is a clique, not a path). -/
def joinsSeg (G : GPathM) (seg : List PathNodeId) (low c : PathNodeId) : Bool :=
  (parentsL G low).contains c && (sonsL G c).contains low
    && seg.all (fun q => (ownersL G q).contains c && (ownersL G c).contains q)

/-- The whole of `SoundOn G seg lo`, with `seg` lowest-first on contiguous steps. -/
def soundSeg (G : GPathM) (seg : List PathNodeId) (lo : Int) : Bool :=
  let idx := (List.range seg.length).map (fun i => lo + Int.ofNat i)
  (seg.zip idx).all (fun pk => pickOk G pk.1 pk.2)
    && (seg.zip (seg.drop 1)).all
        (fun pq => (parentsL G pq.2).contains pq.1 && (sonsL G pq.1).contains pq.2)
    && seg.all (fun p => seg.all (fun q => p == q || (ownersL G q).contains p))

/-- Which condition fails first, for the report. -/
def whyNotSeg (G : GPathM) (seg : List PathNodeId) : Option String := Id.run do
  for p in seg do
    if !(G.node? p).isSome then return some "node absent"
  for p in seg do
    if !G.gowners.contains p then return some "gowner"
  for p in seg do
    if !(ownersL G p).contains p then return some "self_owned"
  -- checked as two independent passes: testing them pairwise in one loop would let the first
  -- `parent_link` failure mask every `son_link` failure in the segment.
  let parentFail := (seg.zip (seg.drop 1)).any (fun pq => !(parentsL G pq.2).contains pq.1)
  let sonFail := (seg.zip (seg.drop 1)).any (fun pq => !(sonsL G pq.1).contains pq.2)
  if parentFail && sonFail then return some "parent_link+son_link"
  if parentFail then return some "parent_link"
  if sonFail then return some "son_link"
  for p in seg do
    for q in seg do
      if p != q && !(ownersL G q).contains p then return some "owned"
  return none

/-- Does `seg` extend by one pick at `lo - 1`? Step 0 is allowed (it is the root).

Candidates are drawn from `parentsL G low` because `SoundOn.parent_link` forces the pick below
`low` to be one of its parents, so nothing outside that list can serve. -/
def extendsDown (G : GPathM) (seg : List PathNodeId) (lo : Int) : Bool :=
  match seg with
  | [] => false
  | low :: _ => (parentsL G low).any (fun c => pickOk G c (lo - 1) && joinsSeg G seg low c)

/-- Why no pick at `lo - 1` works: reports, per candidate, the first condition that rejects it.
Used to tell a genuine dead end from a probe bug. -/
def whyNoExtension (G : GPathM) (seg : List PathNodeId) (lo : Int) : String :=
  match seg with
  | [] => "empty segment"
  | low :: _ =>
    let k := lo - 1
    let cands := (parentsL G low).filter (fun c => c.id.step == k)
    if cands.isEmpty then
      s!"no parent of {showP low} sits at step {k} (of {(parentsL G low).length} parents)"
    else
      let reasons := cands.map (fun c =>
        if !(G.node? c).isSome then s!"{showP c}:absent"
        else if !G.gowners.contains c then s!"{showP c}:not-gowner"
        else if !(ownersL G c).contains c then s!"{showP c}:not-self-owned"
        else if !(if k == 0 then c.parent_id.isNone else c.parent_id.isSome) then
          s!"{showP c}:root-shape"
        else if !(sonsL G c).contains low then s!"{showP c}:no-son-link-back"
        else
          match seg.find? (fun q => !((ownersL G q).contains c && (ownersL G c).contains q)) with
          | some q => s!"{showP c}:not-mutually-owned-with-{showP q}"
          | none => s!"{showP c}:UNEXPECTED-probe-bug")
      s!"{cands.length} candidates at step {k}: " ++ String.intercalate "; " reasons

-- ============================================================
-- Enumerating the partial chains of a state
-- ============================================================

/-- Extend `seg` (lowest-first, lowest at step `lo`) downwards in every possible way, recording
each partial chain reached. Stops at step 1: `SideCovered` only speaks of `0 < lo`. -/
partial def grow (G : GPathM) (seg : List PathNodeId) (lo : Int)
    (out : Array (List PathNodeId × Int)) (b : Nat) : Array (List PathNodeId × Int) × Nat :=
  if b == 0 then (out, 0)
  else if lo - 1 < 1 then (out, b)
  else
    match seg with
    | [] => (out, b)
    | low :: _ =>
      let k := lo - 1
      let cands := (parentsL G low).filter (fun c => pickOk G c k && joinsSeg G seg low c)
      cands.foldl
        (fun (st : Array (List PathNodeId × Int) × Nat) c =>
          if st.2 == 0 then st
          else
            let seg' := c :: seg
            grow G seg' k (st.1.push (seg', k)) (st.2 - 1))
        (out, b)

/-- Every partial chain of `G` on steps `lo .. hi` with `0 < lo ≤ hi < current_step`. -/
def segments (G : GPathM) (budget : Nat) : Array (List PathNodeId × Int) × Nat := Id.run do
  let mut out : Array (List PathNodeId × Int) := #[]
  let mut b := budget
  for hi in (List.range (G.current_step - 1).toNat).map (fun i => (1 : Int) + Int.ofNat i) do
    for n in G.nodes do
      if b != 0 && n.id.id.step == hi && pickOk G n.id hi then
        out := out.push ([n.id], hi)
        let (o, b') := grow G [n.id] hi out (b - 1)
        out := o
        b := b'
  return (out, b)

-- ============================================================
-- Accumulator
-- ============================================================

structure Acc where
  stats : List (String × Nat) := []
  examples : List String := []

def addN (h : List (String × Nat)) (k : String) (v : Nat) : List (String × Nat) :=
  if h.any (fun p => p.1 == k) then h.map (fun p => if p.1 == k then (p.1, p.2 + v) else p)
  else h ++ [(k, v)]

def bump (a : Acc) (k : String) : Acc := { a with stats := addN a.stats k 1 }

def note (a : Acc) (s : String) : Acc :=
  if a.examples.length < 8 then { a with examples := a.examples ++ [s] } else a

-- ============================================================
-- One join
-- ============================================================

def analyseSide (a0 : Acc) (G gs : GPathM) (nm : String)
    (seg : List PathNodeId) (lo : Int) : Acc := Id.run do
  let mut a := a0
  if !seg.all (fun p => (gs.node? p).isSome) then
    return a
  if soundSeg gs seg lo then
    a := bump a s!"[{nm}] picks all inside, already a chain of that side"
  else
    a := bump a s!"[{nm}] picks all inside, BORROWED from the other side"
    match whyNotSeg gs seg with
    | some why => a := bump a s!"[{nm}] borrowed, first failing condition: {why}"
    | none => a := bump a s!"[{nm}] borrowed, classifier disagrees with soundSeg (PROBE BUG)"
    if extendsDown G seg lo then
      a := bump a s!"[{nm}] borrowed AND extends -- SideCovered holds here"
    else
      a := bump a s!"[{nm}] borrowed and DOES NOT extend -- SideCovered FAILS"
      match seg with
      | [] => a := bump a "[??] empty failing segment (PROBE BUG)"
      | low :: _ =>
        if ((parentsL G low).filter (fun c => c.id.step == lo - 1)).isEmpty then
          a := bump a s!"[{nm}] failure shape: no candidate at all at step lo-1"
        else
          a := bump a s!"[{nm}] failure shape: candidates exist, every one rejected"
      a := note a s!"SideCovered fails: side={nm} lo={lo} seg={seg.map showP}"
      a := note a s!"  why: {whyNoExtension G seg lo}"
  return a

def analyseJoin (a0 : Acc) (g1 g2 : GPathM) (segBudget : Nat) : Acc := Id.run do
  let mut a := a0
  if !okJoin g1 g2 then
    return bump a "join skipped (okJoin false, doJoin keeps g1)"
  let G := join g1 g2
  a := bump a "joins analysed"
  let (segs, left) := segments G segBudget
  if left == 0 then
    a := bump a "segment budget exhausted (counts below are partial)"
  for sl in segs do
    let seg := sl.1
    let lo := sl.2
    a := bump a "partial chains of the join"
    let in1 := seg.all (fun p => (g1.node? p).isSome)
    let in2 := seg.all (fun p => (g2.node? p).isSome)
    if !in1 && !in2 then
      a := bump a "DICHOTOMY VIOLATED: picks in neither side alone"
      a := note a s!"cross-side chain lo={lo} seg={seg.map showP}"
    if in1 && in2 then
      a := bump a "picks shared by both sides"
    a := analyseSide a G g1 "g1" seg lo
    a := analyseSide a G g2 "g2" seg lo
  return a

-- ============================================================
-- Driving the machine while keeping both operands of every join
-- ============================================================

structure JoinObs where
  g1 : GPathM
  g2 : GPathM

def insertObs (line : PureLine) (key : NodeId) (g : GPathM) : PureLine × Option JoinObs :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) =>
    (line.map (fun kv => if kv.1 == key then (key, doJoin existing g) else kv),
      some { g1 := existing, g2 := g })
  | none => (line ++ [(key, g)], none)

def sendToObs (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) :
    PureLine × Option JoinObs :=
  let h := upFiltering g (reqOfCnf φ d) d ""
  if isValid h then insertObs next d h else (next, none)

def sendAllObs (φ : Cnf) (kv : NodeId × GPathM) (next : PureLine) :
    PureLine × Array JoinObs :=
  (mapSons φ kv.1.step kv.1.index).foldl
    (fun (st : PureLine × Array JoinObs) d =>
      let (l, o) := sendToObs φ kv.2 st.1 d
      (l, match o with | some j => st.2.push j | none => st.2))
    (next, #[])

def pureAdvanceObs (φ : Cnf) (line : PureLine) : PureLine × Array JoinObs :=
  line.foldl
    (fun (st : PureLine × Array JoinObs) kv =>
      let (l, js) := sendAllObs φ kv st.1
      (l, st.2 ++ js))
    ([], #[])

def runFormula (φ : Cnf) (a0 : Acc) (segBudget : Nat) : Acc := Id.run do
  let mut a := a0
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    let (line', js) := pureAdvanceObs φ line
    for j in js do
      a := analyseJoin a j.g1 j.g2 segBudget
    line := line'
  return a

-- ============================================================
-- Entry point
-- ============================================================

def report (name : String) (a : Acc) : IO Unit := do
  IO.println s!"{name}:"
  for kv in a.stats.mergeSort (fun p q => p.1 ≤ q.1) do
    IO.println s!"  {kv.2}\t{kv.1}"
  for e in a.examples do
    IO.println s!"  EX {e}"

def loadCnf (path : String) : IO (Option Cnf) := do
  let content ← IO.FS.readFile path
  match AbsSat.Cnf.Dimacs.parse (content.splitOn "\n") with
  | .error _ => return none
  | .ok φ => return (if AbsSat.Cnf.Dimacs.wfB φ then some φ else none)

end Probes.JoinBorrow

open Probes.JoinBorrow in
def main (args : List String) : IO Unit := do
  match args with
  | "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf (the machine is strictly 3-SAT: three distinct variables per clause)"
      | some φ => report path (runFormula φ {} 20000)
  | "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
      let mut a : Acc := {}
      for idx in [0:cases.toNat!] do
        let (rng1, nv) := rng.below 3
        let nVars := nvMin.toNat! + nv
        -- every third case is over-constrained, so both SAT and UNSAT runs are covered
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
        | .ok φ => if AbsSat.Cnf.Dimacs.wfB φ then a := runFormula φ a 20000
      report s!"seed {seed}" a
  | _ =>
    IO.println "usage: join-borrow file <cnf>..."
    IO.println "       join-borrow random <cases> <minVars> <seed>..."
