import AbsSat.SatMachine.PureSatMachine
import AbsSat.Cnf.Dimacs
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.SatMachine.DiffTest
import AbsSat.GraphPath.Model.IdSeparator

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
