import AbsSat.SatMachine.PureSatMachine
import AbsSat.Cnf.Dimacs
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.SatMachine.DiffTest
import AbsSat.GraphPath.Model.IdSeparator
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.PureDriverImproves
import AbsSat.Cnf.BruteForce

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

* for every failing chain, whether its pairs are ideal (`coOccurs`: some consistent linked path
  carries both) — stale entries would make the table too rich, missing ideal ones too poor.

**`top` mode** measures `TopPhantom.lean` instead: in every valid filtered state, line state and
final state it enumerates the whole tree of a reader without backtracking from the top, counting
full chains, dead ends and phantom segments, runs five such readers per top node, and prints a full
diagnosis of each phantom (the `FilterNoDeadEnd` hypotheses, picks on consistent paths, ideal pairs).

Usage: `lake exe join-borrow [top] file <cnf>...`,
`lake exe join-borrow [top] random <cases> <minVars> <seed>...`,
`lake exe join-borrow dump <cases> <minVars> <seed> <dir>` (writes the random formulas).
Counterexamples found with it are kept in `Probes/cnf/`.
-/

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.IdSeparator

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
-- Ideal ownership: does a consistent linked path carry this pair?
-- ============================================================

/-- Search budget for one `coOccurs` query. -/
def idealBudget : Nat := 200000

/-- Extend an assignment, failing when a variable would get two values. -/
def addFix (acc : List (Int × Int)) (vv : Int × Int) : Option (List (Int × Int)) :=
  match acc.find? (fun ww => ww.1 == vv.1) with
  | some ww => if ww.2 == vv.2 then some acc else none
  | none => some (vv :: acc)

def addFixes (acc : List (Int × Int)) (vs : List (Int × Int)) : Option (List (Int × Int)) :=
  vs.foldl (fun o vv => match o with | none => none | some x => addFix x vv) (some acc)

/-- Walk upwards along son links from `cur`, keeping the literal assignment consistent and
forcing the path through `a` and `b` at their own steps. True as soon as the top is reached. -/
partial def walk (φ : Cnf) (G : GPathM) (a b cur : PathNodeId)
    (acc : List (Int × Int)) (budget : Nat) : Bool × Nat :=
  if budget == 0 then (false, 0)
  else if cur.id.step + 1 ≥ G.current_step then (true, budget - 1)
  else
    let k := cur.id.step + 1
    let cands := (sonsL G cur).filter (fun s =>
      s.id.step == k && (a.id.step != k || s == a) && (b.id.step != k || s == b))
    cands.foldl
      (fun (st : Bool × Nat) s =>
        if st.1 || st.2 == 0 then st
        else match addFixes acc (fixes φ s) with
          | none => (false, st.2 - 1)
          | some acc' => walk φ G a b s acc' (st.2 - 1))
      (false, budget - 1)

/-- **Is the pair `(a, b)` ideal?** i.e. does some consistent linked path of `G` contain both.
This is the v102 notion of an owner entry that really co-occurs, asked one pair at a time
instead of building the whole ideal table. -/
def coOccurs (φ : Cnf) (G : GPathM) (a b : PathNodeId) (budget : Nat) : Bool × Nat :=
  let starts := G.nodes.filter (fun n =>
    n.id.id.step == 0 && (a.id.step != 0 || n.id == a) && (b.id.step != 0 || n.id == b))
  starts.foldl
    (fun (st : Bool × Nat) n =>
      if st.1 || st.2 == 0 then st
      else match addFixes [] (fixes φ n.id) with
        | none => (false, st.2)
        | some acc => walk φ G a b n.id acc st.2)
    (false, budget)

/-- **(A)** The first ownership pair the chain relies on that no consistent path carries — a
stale entry. Its existence would mean the table is too *rich*, which is what invariant `I`
(ideal owners) would remove. The flag says whether any search was truncated. -/
def firstStalePair (φ : Cnf) (G : GPathM) (seg : List PathNodeId) :
    Option (PathNodeId × PathNodeId) × Bool := Id.run do
  let mut anyOut := false
  for p in seg do
    for q in seg do
      if p != q then
        let (ok, left) := coOccurs φ G p q idealBudget
        if left == 0 then anyOut := true
        else if !ok then return (some (p, q), anyOut)
  return (none, anyOut)

/-- **(B)** The first blocked candidate/pick pair that a consistent path *does* carry — an
ideal entry missing from the table. Its existence would mean the table is too *poor*, which is
the opposite diagnosis and would not be cured by `I`. -/
def firstMissingPair (φ : Cnf) (G : GPathM) (seg : List PathNodeId) (low : PathNodeId)
    (lo : Int) : Option (PathNodeId × PathNodeId) × Bool := Id.run do
  let mut anyOut := false
  for c in (parentsL G low).filter (fun c => c.id.step == lo - 1) do
    for q in seg do
      if !((ownersL G q).contains c && (ownersL G c).contains q) then
        let (ok, left) := coOccurs φ G c q idealBudget
        if left == 0 then anyOut := true
        else if ok then return (some (c, q), anyOut)
  return (none, anyOut)

-- ============================================================
-- Accumulator
-- ============================================================

structure Acc where
  stats : List (String × Nat) := []
  examples : List String := []
  diag : List String := []

def addN (h : List (String × Nat)) (k : String) (v : Nat) : List (String × Nat) :=
  if h.any (fun p => p.1 == k) then h.map (fun p => if p.1 == k then (p.1, p.2 + v) else p)
  else h ++ [(k, v)]

def bump (a : Acc) (k : String) : Acc := { a with stats := addN a.stats k 1 }

def note (a : Acc) (s : String) : Acc :=
  if a.examples.length < 8 then { a with examples := a.examples ++ [s] } else a

-- ============================================================
-- One join
-- ============================================================

def analyseSide (φ : Cnf) (a0 : Acc) (G gs : GPathM) (nm : String)
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
        let (stale, outA) := firstStalePair φ G seg
        if outA then a := bump a s!"[{nm}] (A) some co-occurrence search was truncated"
        match stale with
        | some pq =>
          a := bump a s!"[{nm}] (A) chain USES a stale pair -- table too RICH, I would help"
          a := note a s!"  stale pair: {showP pq.1} with {showP pq.2}"
        | none =>
          a := bump a s!"[{nm}] (A) every pair of the chain is ideal -- I would NOT help"
        let (missing, outB) := firstMissingPair φ G seg low lo
        if outB then a := bump a s!"[{nm}] (B) some co-occurrence search was truncated"
        match missing with
        | some pq =>
          a := bump a s!"[{nm}] (B) a blocked candidate is ideal-but-missing -- table too POOR"
          a := note a s!"  missing pair: {showP pq.1} with {showP pq.2}"
        | none =>
          a := bump a s!"[{nm}] (B) no blocked candidate co-occurs on a consistent path"
      a := note a s!"SideCovered fails: side={nm} lo={lo} seg={seg.map showP}"
      a := note a s!"  why: {whyNoExtension G seg lo}"
  return a

def analyseJoin (φ : Cnf) (a0 : Acc) (g1 g2 : GPathM) (segBudget : Nat) : Acc := Id.run do
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
    a := analyseSide φ a G g1 "g1" seg lo
    a := analyseSide φ a G g2 "g2" seg lo
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
      a := analyseJoin φ a j.g1 j.g2 segBudget
    line := line'
  return a

-- ============================================================
-- Top mode: phantoms anchored at the top of the states the reader reads
-- (`TopPhantom.lean`: `NoDeadEnd g ↔ NoTopPhantom g`)
-- ============================================================

structure TopCount where
  segs : Nat := 0
  full : Nat := 0
  deadEnds : Nat := 0
  phantoms : Nat := 0
  truncated : Bool := false
  ex : Option String := none
  exSeg : Option (List PathNodeId × Int) := none

/-- The picks a reader holding `seg` (lowest at `lo`) could take next: exactly the one-step
extensions of `SoundFrom`. -/
def nextPicks (G : GPathM) (seg : List PathNodeId) (lo : Int) : List PathNodeId :=
  match seg with
  | [] => []
  | low :: _ => (parentsL G low).filter (fun c => pickOk G c (lo - 1) && joinsSeg G seg low c)

/-- The reader's whole tree under `seg`. Returns whether `seg` is real (some descent reaches
step 0); a segment is a phantom when it is not. On budget exhaustion the count is marked
truncated and must not be used. -/
partial def explore (G : GPathM) (seg : List PathNodeId) (lo : Int) (c : TopCount) (b : Nat) :
    Bool × TopCount × Nat :=
  if b == 0 then (true, { c with truncated := true }, 0)
  else
    let c := { c with segs := c.segs + 1 }
    if lo == 0 then (true, { c with full := c.full + 1 }, b - 1)
    else
      match nextPicks G seg lo with
      | [] =>
        (false, { c with deadEnds := c.deadEnds + 1, phantoms := c.phantoms + 1,
                         ex := c.ex.orElse (fun _ => some s!"dead end at lo={lo} seg={seg.map showP}"),
                         exSeg := c.exSeg.orElse (fun _ => some (seg, lo)) },
          b - 1)
      | cands =>
        let (anyReal, c, b) := cands.foldl
          (fun (st : Bool × TopCount × Nat) x =>
            if st.2.2 == 0 then st
            else
              let (r, c', b') := explore G (x :: seg) (lo - 1) st.2.1 st.2.2
              (st.1 || r, c', b'))
          (false, c, b - 1)
        if anyReal then (true, c, b) else (false, { c with phantoms := c.phantoms + 1 }, b)

/-- A reader without backtracking: goes down taking candidate 0 (`seed = 0`) or a
pseudo-random candidate. True when it gets stuck above step 0. -/
partial def readerStuck (G : GPathM) (seg : List PathNodeId) (lo : Int) (seed : Nat) : Bool :=
  if lo == 0 then false
  else
    let cands := nextPicks G seg lo
    if cands.isEmpty then true
    else
      let i := if seed == 0 then 0 else (seed * 2654435761 + lo.toNat * 40503) % cands.length
      match cands[i]? with
      | some x => readerStuck G (x :: seg) (lo - 1) seed
      | none => true

/-- Full chains of `G` (the reader's tree from the top, counted to step 0), budgeted. -/
def fullChains (G : GPathM) (budget : Nat) : Nat × Bool := Id.run do
  if G.current_step < 1 then return (0, false)
  let t := G.current_step - 1
  let mut c : TopCount := {}
  let mut b := budget
  for p in (G.nodes.map (·.id)).filter (fun p => pickOk G p t) do
    if b != 0 then
      let (_, c', b') := explore G [p] t c b
      c := c'
      b := b'
  return (c.full, c.truncated || b == 0)

/-- Everything needed to classify a phantom dead end: the `FilterNoDeadEnd` hypotheses that are
not structural, whether each pick lies on a full chain, and whether every pair is ideal. -/
def diagnosePhantom (φ : Cnf) (ctx : String) (G : GPathM) (pre : Option (GPathM × NodeId))
    (seg : List PathNodeId) (lo : Int) : List String := Id.run do
  let mut out : List String := [s!"=== phantom: {ctx}, top step {G.current_step - 1}, lo={lo}",
    s!"  seg (lowest first) = {seg.map showP}",
    s!"  filtered/read state valid = {isValid G}, full chains in it = {(fullChains G 2000000).1} (truncated {(fullChains G 2000000).2})"]
  match pre with
  | some (g, d) =>
    let (fc, tr) := fullChains g 2000000
    out := out ++ [s!"  FilterNoDeadEnd hypotheses: key d={showP ⟨d, none⟩} d.step={d.step} g.current_step={g.current_step} (equal: {d.step == g.current_step}); d ∈ mapNodes: {(mapNodes φ d.step).contains d}",
      s!"  pre-filter g valid = {isValid g}, full chains of g (denotS non-empty) = {fc} (truncated {tr})"]
  | none => pure ()
  out := out ++ [s!"  why no pick at lo-1: {whyNoExtension G seg lo}"]
  for p in seg do
    let (ok, left) := coOccurs φ G p p idealBudget
    out := out ++ [s!"  pick {showP p}: on a consistent linked path = {ok}{if left == 0 then " (search truncated)" else ""}"]
  let mut ideal := 0
  let mut total := 0
  for p in seg do
    for q in seg do
      if p != q then
        total := total + 1
        let (ok, left) := coOccurs φ G p q idealBudget
        if ok then ideal := ideal + 1
        else out := out ++ [s!"  NON-IDEAL pair {showP p} with {showP q}{if left == 0 then " (search truncated)" else ""}"]
  out := out ++ [s!"  ordered pairs of the segment ideal: {ideal}/{total}"]
  match seg with
  | low :: _ =>
    let (missing, outB) := firstMissingPair φ G seg low lo
    out := out ++ [match missing with
      | some pq => s!"  (B) blocked candidate ideal-but-missing: {showP pq.1} with {showP pq.2}"
      | none => s!"  (B) no blocked candidate co-occurs with its blocker{if outB then " (some search truncated)" else ""}"]
  | [] => pure ()
  return out

def analyseTop (φ : Cnf) (a0 : Acc) (cat : String) (G : GPathM) (budget : Nat)
    (pre : Option (GPathM × NodeId) := none) : Acc := Id.run do
  let mut a := a0
  if G.current_step < 1 then return a
  let t := G.current_step - 1
  let tops := (G.nodes.map (·.id)).filter (fun p => pickOk G p t)
  a := bump a s!"[{cat}] states"
  if tops.isEmpty then
    a := bump a s!"[{cat}] states with no top node"
    return a
  let mut runs := 0
  let mut stuck := 0
  for p in tops do
    for s in [0, 1, 2, 3, 4] do
      runs := runs + 1
      if readerStuck G [p] t s then stuck := stuck + 1
  a := { a with stats := addN (addN a.stats s!"[{cat}] reader runs" runs)
                          s!"[{cat}] reader runs STUCK" stuck }
  let mut c : TopCount := {}
  let mut b := budget
  for p in tops do
    if b != 0 then
      let (_, c', b') := explore G [p] t c b
      c := c'
      b := b'
  if c.truncated || b == 0 then
    a := bump a s!"[{cat}] states truncated (tree over budget, not counted)"
    if stuck > 0 then a := note a s!"{cat} step {t}: reader stuck in a truncated state"
  else
    a := { a with stats := addN (addN (addN (addN a.stats
            s!"[{cat}] top partial chains" c.segs) s!"[{cat}] full chains" c.full)
            s!"[{cat}] DEAD ENDS at the top" c.deadEnds) s!"[{cat}] PHANTOM top segments" c.phantoms }
    if c.deadEnds > 0 then
      a := bump a s!"[{cat}] states WITH phantoms at the top (NoDeadEnd fails)"
      match c.ex with
      | some e => a := note a s!"{cat} step {t}: {e}"
      | none => pure ()
      match c.exSeg with
      | some (seg, lo) => a := { a with diag := a.diag ++ diagnosePhantom φ cat G pre seg lo }
      | none => pure ()
    else
      a := bump a s!"[{cat}] states with no phantom at the top"
      if stuck > 0 then a := bump a s!"[{cat}] reader stuck in a phantom-free state (PROBE BUG)"
  return a

/-- `sendTo`, literally (`upFiltering g reqs d = up (filterAll g reqs) d`), also analysing the
filtered state before the new node is added. -/
def sendToTop (φ : Cnf) (a : Acc) (budget : Nat) (g : GPathM) (next : PureLine) (d : NodeId) :
    PureLine × Acc :=
  let f := filterAll g (reqOfCnf φ d)
  let a := if isValid f then analyseTop φ a "filter" f budget (some (g, d)) else a
  let h := up f d ""
  if isValid h then (insertPure next d h, a) else (next, a)

/-- The pure run, analysing every valid filtered state, every line state, and the final line. -/
def runTop (φ : Cnf) (a0 : Acc) (budget : Nat) : Acc := Id.run do
  let mut a := a0
  let mut line := pureInit φ
  let n := (stepCount φ - 1).toNat
  for i in [0:n] do
    let (line', a') := line.foldl
      (fun (st : PureLine × Acc) kv =>
        (mapSons φ kv.1.step kv.1.index).foldl
          (fun (st2 : PureLine × Acc) d => sendToTop φ st2.2 budget kv.2 st2.1 d) st)
      ([], a)
    a := a'
    line := line'
    let cat := if i + 1 == n then "final" else "line"
    for kv in line do
      a := analyseTop φ a cat kv.2 budget
  a := bump a (if line.isEmpty then "[run] verdict UNSAT (final line empty)"
               else "[run] verdict SAT (final line non-empty)")
  return a

-- ============================================================
-- Read mode: the author's Reader (PathReader.read_step!), traced
-- ============================================================

/-- Values still available for variable `k/2`: map indices of the global owners at value step `k`,
in node order (the Julia reader takes `first(ids)`). -/
def valuesAt (G : GPathM) (k : Int) : List Int :=
  ((G.nodes.map (·.id)).filter (fun p => p.id.step == k && G.gowners.contains p)).foldl
    (fun acc p => if acc.contains p.id.index then acc else acc ++ [p.id.index]) []

def emptyStep (G : GPathM) : Option Int :=
  (List.range G.current_step.toNat).findSome? (fun i =>
    let k : Int := Int.ofNat i
    if G.gowners.any (fun q => q.id.step == k) then none else some k)

def assignOf (vals : List (Int × Int)) : Assign :=
  fun v => (vals.find? (fun kv => kv.1 == (v : Int))).map (fun kv => kv.2 == 1) |>.getD false

structure RStat where
  correct : Nat := 0
  stuck : Nat := 0
  wrong : Nat := 0
  zombiePins : Nat := 0
  lines : Array String := #[]

/-- The whole reading tree: at each value step every available value is pinned
(`filterAll G [value node]`), as the author's reader would if it had chosen it. -/
partial def readTree (φ : Cnf) (G : GPathM) (k : Int) (asg : List (Int × Int)) (st : RStat)
    (traceFirst : Bool) : RStat :=
  if k ≥ litBlock φ then
    let a := assignOf asg
    if satB a φ then { st with correct := st.correct + 1 }
    else
      let st := { st with wrong := st.wrong + 1 }
      if traceFirst then { st with lines := st.lines.push s!"  END: assignment {asg.map (·.2)} is NOT a model" } else st
  else
    let vals := valuesAt G k
    vals.foldl (fun (st : RStat) val =>
      let first := traceFirst && vals.head? == some val
      let G' := filterAll G [{ step := k, index := val }]
      let valid := isValid G'
      let (chains, tr) := if valid then fullChains G' 2000000 else (0, false)
      let plus := if tr then "+" else ""
      let empt := if valid then "" else ", first empty step=" ++ toString (emptyStep G')
      let msg := s!"  x{k / 2 + 1}: available {vals} -> pin {val}: valid={valid}, nodes={G'.nodes.length}, full chains={chains}" ++ plus ++ empt
      let st := if first then { st with lines := st.lines.push msg } else st
      if !valid then
        let st := { st with stuck := st.stuck + 1 }
        if first then { st with lines := st.lines.push "  GRAVE ERROR READER... GPATH INVALID." } else st
      else
        let st := if chains == 0 && !tr then { st with zombiePins := st.zombiePins + 1 } else st
        readTree φ G' (k + 2) (asg ++ [(k / 2, val)]) st first) st

def runRead (φ : Cnf) : IO Unit := do
  let line := pureRun φ
  IO.println s!"final line: {line.length} state(s)"
  for kv in line do
    let G := kv.2
    let (chains, _) := fullChains G 2000000
    IO.println s!"final state key={showP ⟨kv.1, none⟩}: nodes={G.nodes.length}, full chains={chains}"
    for v in List.range φ.nVars do
      IO.println s!"  x{v + 1}: values available at step {2 * v} = {valuesAt G (2 * (v : Int))}"
    IO.println "author's reader (first id at each step):"
    let st := readTree φ G 0 [] {} true
    for l in st.lines do IO.println l
    IO.println s!"all reading choices: correct={st.correct}, stuck (invalid after a pin)={st.stuck}, wrong answer={st.wrong}, valid pins with 0 chains left={st.zombiePins}"

-- ============================================================
-- ValuesOnChains at scale: reader paths, every available value checked
-- ============================================================

structure VStat where
  unsat : Nat := 0
  finalStates : Nat := 0
  paths : Nat := 0
  pathsOk : Nat := 0
  pathsStuck : Nat := 0
  pathsWrong : Nat := 0
  visited : Nat := 0
  valuesChecked : Nat := 0
  stuckPins : Nat := 0
  zombiePins : Nat := 0
  truncated : Nat := 0
  ex : List String := []

def VStat.note (st : VStat) (e : String) : VStat :=
  if st.ex.length < 8 then { st with ex := st.ex ++ [e] } else st

/-- One reader path (`seed = 0` is the author's `first(ids)`), checking at every visited state
every available value: pinning it must keep the state valid and non-empty (`ValuesOnChains`). -/
partial def readPath (φ : Cnf) (G : GPathM) (k : Int) (asg : List (Int × Int)) (seed : Nat)
    (budget : Nat) (st0 : VStat) : VStat := Id.run do
  let mut st := st0
  if k ≥ litBlock φ then
    if satB (assignOf asg) φ then return { st with pathsOk := st.pathsOk + 1 }
    return (({ st with pathsWrong := st.pathsWrong + 1 } : VStat).note s!"wrong answer {asg.map (·.2)}")
  st := { st with visited := st.visited + 1 }
  let vals := valuesAt G k
  let mut pins : Array (Int × GPathM × Bool) := #[]
  for v in vals do
    let G' := filterAll G [{ step := k, index := v }]
    let valid := isValid G'
    st := { st with valuesChecked := st.valuesChecked + 1 }
    if !valid then
      st := ({ st with stuckPins := st.stuckPins + 1 } : VStat).note s!"x{k / 2 + 1}={v}: pin makes the state INVALID (after {asg.map (·.2)})"
    else
      let (c, tr) := fullChains G' budget
      if tr then st := { st with truncated := st.truncated + 1 }
      else if c == 0 then
        st := ({ st with zombiePins := st.zombiePins + 1 } : VStat).note s!"x{k / 2 + 1}={v}: pin valid but NO chain left (after {asg.map (·.2)})"
    pins := pins.push (v, G', valid)
  if pins.isEmpty then return ({ st with pathsStuck := st.pathsStuck + 1 } : VStat).note s!"no value at step {k}"
  let i := if seed == 0 then 0 else (seed * 2654435761 + k.toNat * 40503) % pins.size
  match pins[i]? with
  | some (v, G', true) => return readPath φ G' (k + 2) (asg ++ [(k / 2, v)]) seed budget st
  | _ => return { st with pathsStuck := st.pathsStuck + 1 }

def readFormula (φ : Cnf) (st0 : VStat) (nPaths budget : Nat) : VStat := Id.run do
  let mut st := st0
  let line := pureRun φ
  if line.isEmpty then return { st with unsat := st.unsat + 1 }
  for kv in line do
    st := { st with finalStates := st.finalStates + 1 }
    for seed in List.range nPaths do
      st := readPath φ kv.2 0 [] seed budget { st with paths := st.paths + 1 }
  return st

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

def reportV (name : String) (st : VStat) : IO Unit := do
  IO.println s!"{name}: UNSAT(empty final line)={st.unsat} finalStates={st.finalStates} paths={st.paths} ok={st.pathsOk} STUCK={st.pathsStuck} WRONG={st.pathsWrong}"
  IO.println s!"  reader states visited={st.visited} values checked={st.valuesChecked} ValuesOnChains violations: invalid pins={st.stuckPins}, valid pins with no chain={st.zombiePins}; chain counts truncated={st.truncated}"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- PinsSound: owner entries toward the pinned step, backed by chains?
-- (`ReaderPin.OwnersSoundAt`)
-- ============================================================

/-- Every full chain of `G` (lowest-first, index = step), budgeted. -/
partial def collectChains (G : GPathM) (seg : List PathNodeId) (lo : Int)
    (acc : Array (List PathNodeId)) (b : Nat) : Array (List PathNodeId) × Nat :=
  if b == 0 then (acc, 0)
  else if lo == 0 then (acc.push seg, b - 1)
  else
    (nextPicks G seg lo).foldl
      (fun (st : Array (List PathNodeId) × Nat) x =>
        if st.2 == 0 then st else collectChains G (x :: seg) (lo - 1) st.1 (st.2 - 1))
      (acc, b - 1)

def allChains (G : GPathM) (budget : Nat) : Array (List PathNodeId) × Bool := Id.run do
  if G.current_step < 1 then return (#[], false)
  let t := G.current_step - 1
  let mut acc : Array (List PathNodeId) := #[]
  let mut b := budget
  for p in (G.nodes.map (·.id)).filter (fun p => pickOk G p t) do
    if b != 0 then
      let (a, b') := collectChains G [p] t acc b
      acc := a
      b := b'
  return (acc, b == 0)

structure SStat where
  states : Nat := 0
  truncated : Nat := 0
  entries : Nat := 0
  unbacked : Nat := 0
  unbackedSurvive : Nat := 0
  pinnedEntries : Nat := 0
  unbackedPinned : Nat := 0
  pathsOk : Nat := 0
  pathsBad : Nat := 0
  ex : List String := []

/-- Along one author path: before each pin at step `k`, every owner entry `(x, q)` with `q` a global
owner at step `k` must lie on a common chain (`OwnersSoundAt`). An unbacked entry whose node `x`
survives the chosen pin is the dangerous kind. -/
partial def soundPath (φ : Cnf) (G : GPathM) (k : Int) (seed : Nat) (budget : Nat) (st0 : SStat) :
    SStat := Id.run do
  let mut st := st0
  if k ≥ litBlock φ then return { st with pathsOk := st.pathsOk + 1 }
  let vals := valuesAt G k
  if vals.isEmpty then return { st with pathsBad := st.pathsBad + 1 }
  let i := if seed == 0 then 0 else (seed * 2654435761 + k.toNat * 40503) % vals.length
  let val := vals[i]?.getD 0
  let d : NodeId := { step := k, index := val }
  let G' := filterAll G [d]
  let (chains, tr) := allChains G budget
  st := { st with states := st.states + 1 }
  if tr then
    st := { st with truncated := st.truncated + 1 }
  else
    for n in G.nodes do
      for q in ownersAt n.owners k do
        if G.gowners.contains q then
          st := { st with entries := st.entries + 1 }
          let x := n.id
          let backed := chains.any (fun c => c.contains x && c.contains q)
          if q.id == d then
            st := { st with pinnedEntries := st.pinnedEntries + 1 }
            if !backed then st := { st with unbackedPinned := st.unbackedPinned + 1 }
          if !backed then
            st := { st with unbacked := st.unbacked + 1 }
            if q.id == d && (G'.node? x).isSome then
              st := { st with unbackedSurvive := st.unbackedSurvive + 1 }
              if st.ex.length < 8 then
                st := { st with ex := st.ex ++ [s!"step {k} pin {val}: node {showP x} survives via unbacked entry {showP q}"] }
  if !isValid G' then return { st with pathsBad := st.pathsBad + 1 }
  return soundPath φ G' (k + 2) seed budget st

def soundFormula (φ : Cnf) (st0 : SStat) (nPaths budget : Nat) : SStat := Id.run do
  let mut st := st0
  for kv in pureRun φ do
    for seed in List.range nPaths do
      st := soundPath φ kv.2 0 seed budget st
  return st

def reportS (name : String) (st : SStat) : IO Unit := do
  IO.println s!"{name}: reader states={st.states} (truncated {st.truncated}) paths ok={st.pathsOk} bad={st.pathsBad}"
  IO.println s!"  owner entries toward the pinned step={st.entries}, NOT backed by a chain={st.unbacked}, of which the node survives the pin={st.unbackedSurvive}"
  IO.println s!"  entries naming the pinned value={st.pinnedEntries}, NOT backed={st.unbackedPinned}"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Trace mode: where does the first zombie state (valid, no chain) appear?
-- ============================================================

partial def hasChainFrom (G : GPathM) (seg : List PathNodeId) (lo : Int) (b : Nat) : Bool × Nat :=
  if b == 0 then (false, 0)
  else if lo == 0 then (true, b - 1)
  else
    (nextPicks G seg lo).foldl
      (fun (st : Bool × Nat) x =>
        if st.1 || st.2 == 0 then st else hasChainFrom G (x :: seg) (lo - 1) (st.2 - 1))
      (false, b - 1)

/-- `some true`: a full chain exists; `some false`: none; `none`: search truncated. -/
def hasChain (G : GPathM) (budget : Nat) : Option Bool := Id.run do
  if G.current_step < 1 then return some false
  let t := G.current_step - 1
  let mut b := budget
  for p in (G.nodes.map (·.id)).filter (fun p => pickOk G p t) do
    if b != 0 then
      let (found, b') := hasChainFrom G [p] t b
      if found then return some true
      b := b'
  return if b == 0 then none else some false

def describeStep (φ : Cnf) (k : Int) : String :=
  if k < litBlock φ then s!"x{k / 2 + 1}" ++ (if k % 2 == 0 then " value" else " negation")
  else if k == litBlock φ then "fusion"
  else if k < fusionTop φ then s!"clause {k - (litBlock φ + 1)}"
  else "end"

def showPin (φ : Cnf) (r : NodeId) : String :=
  match varVal φ r with
  | some (v, b) => s!"x{v + 1}={b}@{r.step}"
  | none => s!"{describeStep φ r.step}#{r.index}@{r.step}"

def subsetsBelow {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest => let r := subsetsBelow rest; r ++ r.map (a :: ·)

def runTrace (φ : Cnf) : IO Unit := do
  let mut line := pureInit φ
  let n := (stepCount φ - 1).toNat
  for i in [0:n] do
    let line' := pureAdvance φ line
    let mut zombies : List NodeId := []
    let mut trunc := 0
    for kv in line' do
      match hasChain kv.2 3000000 with
      | some false => zombies := zombies ++ [kv.1]
      | none => trunc := trunc + 1
      | _ => pure ()
    IO.println s!"step {i + 1} ({describeStep φ (i + 1)}): states={line'.length} zombies={zombies.length} truncated={trunc}"
    if !zombies.isEmpty then
      IO.println s!"FIRST ZOMBIE STEP {i + 1}: keys {zombies.map (fun z => showP ⟨z, none⟩)}"
      for kv in line do
        for d in mapSons φ kv.1.step kv.1.index do
          if zombies.contains d then
            let g := kv.2
            let reqs := reqOfCnf φ d
            let f := filterAll g reqs
            if isValid f then
              IO.println s!"  send {showP ⟨kv.1, none⟩} -> {showP ⟨d, none⟩}: source nodes={g.nodes.length} has chain={hasChain g 3000000}; filtered nodes={f.nodes.length} VALID, has chain={hasChain f 3000000}"
              IO.println s!"    pins: {reqs.map (showPin φ)}"
              for sub in subsetsBelow reqs do
                if sub.length < reqs.length && sub.length > 0 then
                  let fs := filterAll g sub
                  IO.println s!"    pins subset {sub.map (showPin φ)}: valid={isValid fs}, has chain={hasChain fs 3000000}"
      return
    line := line'
  IO.println "no zombie state along the run"

-- ============================================================
-- Agg mode: the Improves driver with the aggressive review, before wiring it into the machine
-- ============================================================

open AbsSat.GraphPath.Model.AggressiveReview in
open AbsSat.GraphPath.Model.PureDriverImproves in
open AbsSat.GraphMap.CnfMapImproves in
def pureRunAggW (φ : Cnf) : PureLine := Id.run do
  let mut line := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    line := line.foldl (fun next kv =>
      (mapSons φ kv.1.step kv.1.index).foldl (fun next d =>
        let h := up (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d ""
        if isValid h then insertPure next d h else next) next) []
  return line

open AbsSat.GraphPath.Model.PureDriverImproves in
def runAggCompare (path : String) (φ : Cnf) : IO Unit := do
  let t0 ← IO.monoMsNow
  let base ← IO.lazyPure (fun _ => pureRunW φ)
  let nb := base.length
  let t1 ← IO.monoMsNow
  let agg ← IO.lazyPure (fun _ => pureRunAggW φ)
  let na := agg.length
  let t2 ← IO.monoMsNow
  IO.println s!"  (final line sizes: base {nb}, aggressive {na})"
  let oracle := !(AbsSat.Cnf.bruteForceSat φ).isEmpty
  IO.println s!"{path}: oracle SAT={oracle} | improves (base review) SAT={!base.isEmpty} {t1 - t0}ms | improves + aggressive review SAT={!agg.isEmpty} {t2 - t1}ms{if (!agg.isEmpty) != oracle then "  <-- MISMATCH" else ""}"

-- ============================================================
-- Readagg mode: the reader over the aggressive review (`ReaderAgg.PickSomeAgg`), measured
-- ============================================================

structure AStat where
  formulas : Nat := 0
  oracleSat : Nat := 0
  machineSat : Nat := 0
  verdictWrong : Nat := 0
  states : Nat := 0
  starts : Nat := 0
  ok : Nat := 0
  wrong : Nat := 0
  stuck : Nat := 0
  visited : Nat := 0
  pinsTried : Nat := 0
  invalidPins : Nat := 0
  firstStepDead : Nat := 0
  ex : List String := []

def AStat.note (st : AStat) (e : String) : AStat :=
  if st.ex.length < 8 then { st with ex := st.ex ++ [e] } else st

open AbsSat.GraphPath.Model.AggressiveReview in
open AbsSat.GraphPath.Model.PickInduction in
/-- The reading loop of `ReaderAgg`: while some step has a choice, pin a map node there with the
aggressive review and keep the first pin that leaves the graph valid (steps bottom-up, ids in node
order, rotated by `seed`). Stuck = no valid pin at any step with a choice (`PickSomeAgg` fails). At
the end (no choice left) a final state must spell a model. -/
partial def readAggLoop (φ : Cnf) (final : Bool) (G : GPathM) (seed depth : Nat) (st0 : AStat) :
    AStat := Id.run do
  let mut st := { st0 with visited := st0.visited + 1 }
  if !hasChoice G then
    if !final then return { st with ok := st.ok + 1 }
    let a : Assign := fun v => (valuesAt G (2 * (v : Int))).head? == some 1
    if satB a φ then return { st with ok := st.ok + 1 }
    return ({ st with wrong := st.wrong + 1 } : AStat).note s!"no choice left, but not a model (depth {depth})"
  let ks := (intRange 0 (G.current_step - 1)).filter (choiceAt G)
  let mut found : Option GPathM := none
  let mut firstK := true
  for k in ks do
    if found.isNone then
      let ids0 := ((ownersAt G.gowners k).map (·.id)).eraseDups
      let ids := if seed == 0 || ids0.isEmpty then ids0 else (ids0.drop ((seed + depth) % ids0.length) ++ ids0.take ((seed + depth) % ids0.length))
      for id in ids do
        if found.isNone then
          let G' := filterAllAgg G [id]
          st := { st with pinsTried := st.pinsTried + 1 }
          if isValid G' then found := some G'
          else st := { st with invalidPins := st.invalidPins + 1 }
      if found.isNone && firstK then st := { st with firstStepDead := st.firstStepDead + 1 }
      firstK := false
  match found with
  | some G' => return readAggLoop φ final G' seed (depth + 1) st
  | none =>
    return ({ st with stuck := st.stuck + 1 } : AStat).note
      s!"PickSomeAgg FAILS: depth {depth}, step {G.current_step}, nodes {G.nodes.length}, choice steps {ks.length}"

open AbsSat.GraphPath.Model.AggressiveReview in
open AbsSat.GraphPath.Model.PureDriverImproves in
open AbsSat.GraphMap.CnfMapImproves in
/-- Every line of the Improves driver with the aggressive review. -/
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

open AbsSat.GraphPath.Model.AggressiveReview in
/-- Run the reader from every final state (`allLines = false`) or from every state of every line. -/
def readAggFormula (φ : Cnf) (st0 : AStat) (nPaths : Nat) (allLines : Bool) : AStat := Id.run do
  let lines := aggLines φ
  let finalLine := lines.getLastD []
  let oracle := !(AbsSat.Cnf.bruteForceSat φ).isEmpty
  let mut st : AStat := { st0 with formulas := st0.formulas + 1 }
  if oracle then st := { st with oracleSat := st.oracleSat + 1 }
  if !finalLine.isEmpty then st := { st with machineSat := st.machineSat + 1 }
  if oracle == finalLine.isEmpty then
    st := ({ st with verdictWrong := st.verdictWrong + 1 } : AStat).note s!"VERDICT WRONG (oracle SAT={oracle})"
  let n := lines.length
  let mut i := 0
  for line in lines do
    i := i + 1
    let final := i == n
    if allLines || final then
      for kv in line do
        let G := filterAllAgg kv.2 []
        st := { st with states := st.states + 1 }
        if isValid G then
          for seed in List.range (if final then nPaths else 1) do
            st := readAggLoop φ final G seed 0 { st with starts := st.starts + 1 }
  return st

def reportA (name : String) (st : AStat) (ms : Nat) : IO Unit := do
  IO.println s!"{name}: formulas={st.formulas} oracleSAT={st.oracleSat} machineSAT={st.machineSat} verdictWrong={st.verdictWrong} | states={st.states} readerRuns={st.starts} ok={st.ok} STUCK={st.stuck} WRONG={st.wrong} | visited={st.visited} pins={st.pinsTried} invalidPins={st.invalidPins} firstChoiceStepDead={st.firstStepDead} | {ms}ms"
  for e in st.ex do IO.println s!"  EX {e}"

-- ============================================================
-- Entry point
-- ============================================================

def report (name : String) (a : Acc) : IO Unit := do
  IO.println s!"{name}:"
  for kv in a.stats.mergeSort (fun p q => p.1 ≤ q.1) do
    IO.println s!"  {kv.2}\t{kv.1}"
  for e in a.examples do
    IO.println s!"  EX {e}"
  for l in a.diag do
    IO.println l

def loadCnf (path : String) : IO (Option Cnf) := do
  let content ← IO.FS.readFile path
  match AbsSat.Cnf.Dimacs.parse (content.splitOn "\n") with
  | .error _ => return none
  | .ok φ => return (if AbsSat.Cnf.Dimacs.wfB φ then some φ else none)

end Probes.JoinBorrow

open Probes.JoinBorrow in
def main (args : List String) : IO Unit := do
  let top := args.head? == some "top"
  let args := if top then args.drop 1 else args
  let run (φ : Cnf) (a : Acc) : Acc := if top then runTop φ a 300000 else runFormula φ a 20000
  match args with
  | "readagg" :: "random" :: cases :: nvMin :: nPaths :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut st : AStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := readAggFormula φ st nPaths.toNat! false
      let t1 ← IO.monoMsNow
      reportA s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" st (t1 - t0)
  | "readagg" :: "all" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => readAggFormula φ {} 1 true)
        let t1 ← IO.monoMsNow
        reportA s!"{path} [all lines]" st (t1 - t0)
  | "readagg" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let st ← IO.lazyPure (fun _ => readAggFormula φ {} 5 false)
        let t1 ← IO.monoMsNow
        reportA path st (t1 - t0)
  | "agg" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let mut i := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        runAggCompare s!"seed {seed} #{i}" φ
        i := i + 1
  | "agg" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ => runAggCompare path φ
  | "trace" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        IO.println s!"=== {path}"
        runTrace φ
  | "sound" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let mut st : SStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := soundFormula φ st 5 200000
      reportS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" st
  | "sound" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ => reportS path (soundFormula φ {} 5 200000)
  | "read" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let mut st : VStat := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        st := readFormula φ st 9 200000
      reportV s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" st
  | "read" :: "paths" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ => reportV path (readFormula φ {} 9 200000)
  | "read" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        IO.println s!"=== {path}"
        runRead φ
  | "dump" :: cases :: nvMin :: seed :: dir :: _ =>
    let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed.toNat!
    for idx in [0:cases.toNat!] do
      let (rng1, nv) := rng.below 3
      let nVars := nvMin.toNat! + nv
      let (rng2, nClauses) :=
        if idx % 3 == 2 then
          let (r, extra) := rng1.below (2 * nVars + 1)
          (r, 4 * nVars + extra)
        else
          let (r, nc) := rng1.below (4 * nVars)
          (r, 1 + nc)
      let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
      rng := rng3
      IO.FS.writeFile s!"{dir}/s{seed}_{idx}.cnf" cnf
      IO.println s!"{dir}/s{seed}_{idx}.cnf: {nVars} vars, {nClauses} clauses"
  | "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf (the machine is strictly 3-SAT: three distinct variables per clause)"
      | some φ => report path (run φ {})
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
        | .ok φ => if AbsSat.Cnf.Dimacs.wfB φ then a := run φ a
      report s!"seed {seed}" a
  | _ =>
    IO.println "usage: join-borrow [top] file <cnf>..."
    IO.println "       join-borrow [top] random <cases> <minVars> <seed>..."
