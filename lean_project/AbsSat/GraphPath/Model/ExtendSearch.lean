-- lean_project/AbsSat/GraphPath/Model/ExtendSearch.lean
import AbsSat.GraphPath.Model.Extendable
import AbsSat.GraphPath.Model.Pinned
import AbsSat.GraphPath.Model.Survive
import AbsSat.GraphPath.Model.PickInduction
import AbsSat.GraphPath.Model.Validate
import AbsSat.GraphPath.Model.MirrorTest
import AbsSat.GraphMap.ImportCnf
import AbsSat.SatMachine.DiffTest

/-!
`lake exe extend` — the falsifier for route A.

`Extendable.lean` proves `ExtendUp → ExtendDown → Supported`, so
backtrack-freeness would close L6. But `Extendable` is **strictly stronger**
than `Supported`: a pair of nodes can own each other and still lie on no
common chain, which leaves every node supported while a non-backtracking
search is stuck. Whether the machine's pruning rules that out is the question
route A lives or dies on, and it is decidable on real maps.

**What is searched.** For every node of every valid state, the singleton
partial chain at that node is explored *in both directions*, over **all**
consistent continuations, not one. A partial chain with no consistent
continuation and steps left to fill is a counterexample to `ExtendUp` /
`ExtendDown` — a place where a non-backtracking reader would stop.

**Cost.** If the property holds the exploration never branches into a dead
end, so it is cheap; if it fails it stops at the first witness. A budget
bounds the exploration anyway, and a run that exhausts it is reported as
**inconclusive** rather than clean — a search that gave up must not be read as
a search that found nothing.
-/

namespace AbsSat.GraphPath.Model.ExtendSearch

open AbsSat.Utils.Alias
open AbsSat.GraphMap.GraphMap AbsSat.GraphMap.ImportCnf
open AbsSat.GraphPath.Model AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MirrorTest
open L6Search (ownersOfB)

/-- Mutual ownership with every node already chosen — `PairwiseOwned` read on
the picks made so far. -/
def coOwned (g : GPathM) (chosen : List PathNodeId) (c : PathNodeId) : Bool :=
  chosen.all (fun q => (ownersOfB g q).contains c && (ownersOfB g c).contains q)

def parentsOf (g : GPathM) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with | some n => n.parents | none => []

/-- `chosen` is kept ordered by step, highest first. -/
def candsUp (g : GPathM) (chosen : List PathNodeId) (k : Int) : List PathNodeId :=
  ((g.line k).map (·.id)).filter (fun c =>
    (match chosen with
     | [] => true
     | top :: _ => (parentsOf g c).contains top)
    && coOwned g chosen c)

def candsDown (g : GPathM) (chosen : List PathNodeId) (k : Int) : List PathNodeId :=
  ((g.line k).map (·.id)).filter (fun c =>
    (match chosen.getLast? with
     | none => true
     | some bot => (parentsOf g bot).contains c)
    && coOwned g chosen c)

/-- A stuck partial chain, or the remaining budget. `.ok 0` means the budget
ran out: inconclusive, not clean. -/
abbrev Outcome := Except (List PathNodeId) Nat

partial def exploreUp (g : GPathM) (chosen : List PathNodeId) (hi : Int)
    (budget : Nat) : Outcome :=
  if budget = 0 then .ok 0
  else if hi + 1 ≥ g.current_step then .ok (budget - 1)
  else
    let cs := candsUp g chosen (hi + 1)
    if cs.isEmpty then .error chosen
    else cs.foldl (fun st c =>
      match st with
      | .error e => .error e
      | .ok 0 => .ok 0
      | .ok b => exploreUp g (c :: chosen) (hi + 1) (b - 1)) (.ok (budget - 1))

partial def exploreDown (g : GPathM) (chosen : List PathNodeId) (lo : Int)
    (budget : Nat) : Outcome :=
  if budget = 0 then .ok 0
  else if lo ≤ 0 then .ok (budget - 1)
  else
    let cs := candsDown g chosen (lo - 1)
    if cs.isEmpty then .error chosen
    else cs.foldl (fun st c =>
      match st with
      | .error e => .error e
      | .ok 0 => .ok 0
      | .ok b => exploreDown g (chosen ++ [c]) (lo - 1) (b - 1)) (.ok (budget - 1))

/-- `(up failures, down failures, budget exhausted?, first witness)` for one
graph. The two directions are counted apart on purpose: they are different
obligations, and only one of them is what a reader walking upward from step 0
needs. -/
def probe (g : GPathM) (budget : Nat) : Nat × Nat × Bool × Option (String × List PathNodeId) :=
  g.nodes.foldl (fun (acc : Nat × Nat × Bool × Option (String × List PathNodeId)) n =>
    let s := n.id.id.step
    let up := exploreUp g [n.id] s budget
    let down := exploreDown g [n.id] s budget
    let bu := (match up with | .error _ => 1 | .ok _ => 0)
    let bd := (match down with | .error _ => 1 | .ok _ => 0)
    let out := (match up with | .ok 0 => true | _ => false)
             || (match down with | .ok 0 => true | _ => false)
    let wit := match acc.2.2.2 with
      | some w => some w
      | none => match up, down with
                | .error e, _ => some ("up", e)
                | _, .error e => some ("down", e)
                | _, _ => none
    (acc.1 + bu, acc.2.1 + bd, acc.2.2.1 || out, wit)) (0, 0, false, none)

/-- Total failures, either direction. -/
def probeBad (g : GPathM) (budget : Nat) : Nat :=
  let p := probe g budget
  p.1 + p.2.1

/-- Does some step of `g` hold more than one node? A state with no branching
cannot exhibit a stuck chain, so counting these keeps a clean run honest. -/
def branching (g : GPathM) : Bool :=
  (intRange 0 (g.current_step - 1)).any (fun k => (g.line k).length > 1)

-- ============================================================
-- With propagation: the reader's own semantics (`ReadStable`)
-- ============================================================

def dedupNodeIds (ids : List NodeId) : List NodeId :=
  ids.foldl (fun acc id => if acc.contains id then acc else acc ++ [id]) []

/-- The search above checks pairwise co-ownership only. The **reader
propagates**: after every pick it runs `filterAll`, which prunes everything
incompatible with the selection, and continues in the *filtered* graph. So the
property the reader needs is not the pairwise one but
`Verdict.ReadStable` — `Supported` preserved by that filter.

`readStableStep` is its one-step form: selecting any surviving map node keeps
the graph valid. -/
def readStableStep (g : GPathM) : Nat :=
  let mids := dedupNodeIds (g.nodes.map (·.id.id))
  (mids.filter (fun mid => !isValid (filterAll g [mid]))).length

/-- And its transitive form: read the graph the way the reader does — pick,
propagate, recurse — over **every** branch, and report a pick that invalidates
the graph. `.error` carries the step it happened at. -/
partial def exploreFiltered (g : GPathM) (k : Int) (budget : Nat) : Except Int Nat :=
  if budget = 0 then .ok 0
  else if k ≥ g.current_step then .ok (budget - 1)
  else
    let mids := dedupNodeIds ((g.line k).map (·.id.id))
    if mids.isEmpty then .error k
    else mids.foldl (fun st mid =>
      match st with
      | .error e => .error e
      | .ok 0 => .ok 0
      | .ok b =>
        let g' := filterAll g [mid]
        if isValid g' then exploreFiltered g' (k + 1) (b - 1) else .error k)
      (.ok (budget - 1))

abbrev Acc := Nat × Nat × Nat × Nat × Nat × Bool × Option (String × List PathNodeId)

abbrev RAcc := Nat × Nat × Nat × Nat × Bool

/-- `(states, nodes, one-step ReadStable failures, transitive failures,
budget exhausted)`. -/
partial def walkRead (gmap : GMap) (line : MirrorLine) (fuel budget : Nat)
    (acc : RAcc) : RAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : RAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let one := readStableStep g
        let (tr, out) := match exploreFiltered g 0 budget with
          | .error _ => (1, false)
          | .ok 0 => (0, true)
          | .ok _ => (0, false)
        (a.1 + 1, a.2.1 + g.nodes.length, a.2.2.1 + one, a.2.2.2.1 + tr,
         a.2.2.2.2 || out)) acc
    walkRead gmap (mirrorAdvance gmap line) (fuel - 1) budget acc

def reportRead (path : String) (budget : Nat) : IO Bool := do
  let gmap ← load_import! path
  let (states, nodes, one, tr, out) := walkRead gmap (mirrorInit gmap) 1000 budget (0, 0, 0, 0, false)
  IO.println s!"{path}"
  IO.println s!"  valid states={states}  nodes={nodes}  budget exhausted={out}"
  if one + tr == 0 then
    let note := if out then " (INCONCLUSIVE: budget hit)" else ""
    IO.println s!"  ReadStable holds: every pick propagates to a still-valid graph{note}"
    return !out
  else
    IO.println s!"  BROKEN: one-step failures={one}, whole-read failures={tr} — ReadStable FAILS"
    return false

/-- Walk every state the machine holds.
`(states, branching, nodes, up failures, down failures, budget exhausted,
first witness)`. -/
partial def walk (gmap : GMap) (line : MirrorLine) (fuel budget : Nat)
    (acc : Acc) : Acc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : Acc) kv =>
      let g := kv.2
      if !isValid g then a else
        let (bu, bd, out, wit) := probe g budget
        (a.1 + 1, a.2.1 + (if branching g then 1 else 0), a.2.2.1 + g.nodes.length,
         a.2.2.2.1 + bu, a.2.2.2.2.1 + bd, a.2.2.2.2.2.1 || out,
         match a.2.2.2.2.2.2 with | some w => some w | none => wit)) acc
    walk gmap (mirrorAdvance gmap line) (fuel - 1) budget acc

def emptyAcc : Acc := (0, 0, 0, 0, 0, false, none)

def report (path : String) (budget : Nat) : IO Bool := do
  let gmap ← load_import! path
  let (states, branch, nodes, bu, bd, out, wit) :=
    walk gmap (mirrorInit gmap) 1000 budget emptyAcc
  IO.println s!"{path}"
  IO.println s!"  valid states={states} (branching {branch})  nodes={nodes}  budget exhausted={out}"
  if bu + bd == 0 then
    let note := if out then " (INCONCLUSIVE: budget hit)" else ""
    IO.println s!"  Extendable holds: no stuck partial chain{note}"
    return !out
  else
    IO.println s!"  STUCK: up={bu} down={bd} dead-end partial chain(s) — Extendable FAILS"
    match wit with
    | some (dir, w) =>
      IO.println s!"  first witness ({dir}): {w.map toString}"
    | none => pure ()
    return false

-- ============================================================
-- The sharper experiment: arbitrary requirements, no 3SAT structure
-- ============================================================

/-- The same probe over `L6Search`'s synthetic maps, whose requirements obey
only `Reachable`'s own hypotheses and carry **no 3SAT structure at all**. If
`Extendable` fails here but holds on real maps, the map construction is doing
the work; if it holds here too, the machine's pruning is.
`(states, branching, stuck, budget exhausted)`. -/
def probeSynthetic (steps width trials budget : Nat) : Nat × Nat × Nat × Bool :=
  (List.range trials).foldl (fun (acc : Nat × Nat × Nat × Bool) t =>
    let m : L6Search.SynMap :=
      { steps := steps, width := width, reqs := L6Search.mkReqs width (t * 7919 + 1) }
    (L6Search.runMapAll m).foldl (fun a line =>
      line.foldl (fun (b : Nat × Nat × Nat × Bool) kv =>
        let g := kv.2
        if !isValid g then b else
          let (bu, bd, out, _) := probe g budget
          (b.1 + 1, b.2.1 + (if branching g then 1 else 0), b.2.2.1 + bu + bd,
           b.2.2.2 || out)) a) acc) (0, 0, 0, false)

def runSynthetic (steps width trials budget : Nat) : IO UInt32 := do
  IO.println s!"--- Extendable over synthetic maps (no 3SAT structure): steps={steps} width={width} trials={trials} ---"
  let (states, branch, stuck, out) := probeSynthetic steps width trials budget
  IO.println s!"  valid states={states} (branching {branch})  budget exhausted={out}"
  if stuck == 0 then
    IO.println "  no stuck partial chain: Extendable survives arbitrary requirements too. ✅"
    pure 0
  else
    IO.println s!"  STUCK: {stuck} dead-end partial chain(s) — Extendable is FALSE for arbitrary requirements. The 3SAT structure would have to be what saves it. ❌"
    pure 1

open AbsSat.SatMachine.DiffTest (Rng gen_cnf)

def runRandom (cases seed nvMin nvSpan budget : Nat) : IO UInt32 := do
  IO.println s!"--- Extendable (backtrack-free) campaign: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} budget={budget} ---"
  let mut rng := Rng.ofSeed seed
  let mut failures := 0
  let mut inconclusive := 0
  let mut states := 0
  let mut branch := 0
  let mut nodes := 0
  let mut stuck := 0
  let mut ups := 0
  let mut downs := 0
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let (st, br, nd, bu, bd, out, _) := walk gmap (mirrorInit gmap) 1000 budget emptyAcc
    let bad := bu + bd
    states := states + st
    branch := branch + br
    nodes := nodes + nd
    ups := ups + bu
    downs := downs + bd
    stuck := stuck + bad
    if bad != 0 then
      failures := failures + 1
      IO.FS.writeFile s!"extend_failure_{idx}.cnf" cnf
      IO.println s!"  STUCK at case {idx} (vars={nVars} clauses={nClauses}) \
-> extend_failure_{idx}.cnf"
    else if out then
      inconclusive := inconclusive + 1
  IO.println s!"--- {cases - failures - inconclusive}/{cases} backtrack-free; \
{inconclusive} inconclusive (budget); states={states} (branching {branch}) nodes={nodes} stuck={stuck} (up={ups} down={downs}) ---"
  if failures == 0 then
    IO.println "No partial chain ever got stuck. Extendable survives. ✅"
    pure 0
  else
    IO.println s!"{failures} instance(s) where a partial chain is stuck: Extendable is FALSE. ❌"
    pure 1

/-- The same campaign, for `ReadStable` — pick, propagate, recurse. -/
def runRandomRead (cases seed nvMin nvSpan budget : Nat) : IO UInt32 := do
  IO.println s!"--- ReadStable (pick + propagate) campaign: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut failures := 0
  let mut inconclusive := 0
  let mut states := 0
  let mut nodes := 0
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let (st, nd, one, tr, out) := walkRead gmap (mirrorInit gmap) 1000 budget (0, 0, 0, 0, false)
    states := states + st
    nodes := nodes + nd
    if one + tr != 0 then
      failures := failures + 1
      IO.FS.writeFile s!"extend_failure_{idx}.cnf" cnf
      IO.println s!"  READSTABLE BROKEN at case {idx} (vars={nVars} clauses={nClauses}) \
one-step={one} whole-read={tr}"
    else if out then
      inconclusive := inconclusive + 1
  IO.println s!"--- {cases - failures - inconclusive}/{cases} ReadStable; \
{inconclusive} inconclusive (budget); states={states} nodes={nodes} ---"
  if failures == 0 then
    IO.println "Every pick propagates to a still-valid graph. ReadStable survives. ✅"
    pure 0
  else
    IO.println s!"{failures} instance(s) where propagation breaks the graph. ❌"
    pure 1

-- ============================================================
-- Route A' — running the descent `PickInduction` reasons about
-- ============================================================

open AbsSat.GraphPath.Model.PickInduction (hasChoice choiceAt)

/-- The first global owner sitting at a step where the owners still disagree —
the pick `Inhabited_of_descent` makes. -/
def firstChoice (g : GPathM) : Option PathNodeId :=
  (intRange 0 (g.current_step - 1)).findSome? (fun k =>
    if choiceAt g k then (ownersAt g.gowners k).head? else none)

/-- Run the descent: pick, propagate, repeat, until nothing is left to choose.
`.error` means a pick broke validity — a violation of `PickValid`, the one
obligation route A' still owes. -/
partial def descend (g : GPathM) (fuel : Nat) : Except String GPathM :=
  if fuel = 0 then .error "fuel exhausted"
  else if !hasChoice g then .ok g
  else
    match firstChoice g with
    | none => .ok g
    | some q =>
      let g' := filterAll g [q.id]
      if isValid g' then descend g' (fuel - 1)
      else .error s!"PickValid violated: selecting {q.id} invalidated the graph"

/-- `(states, descents completed, PickValid violations, no-choice endpoints
with a verified chain, no-choice endpoints without one)`. -/
abbrev DAcc := Nat × Nat × Nat × Nat × Nat

partial def walkDescend (gmap : GMap) (line : MirrorLine) (fuel : Nat)
    (acc : DAcc) : DAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : DAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        match descend g 10000 with
        | .error _ => (a.1 + 1, a.2.1, a.2.2.1 + 1, a.2.2.2.1, a.2.2.2.2)
        | .ok g' =>
          let cert := Validate.inhabitCert g'
          if Certificate.isCert g' cert then
            (a.1 + 1, a.2.1 + 1, a.2.2.1, a.2.2.2.1 + 1, a.2.2.2.2)
          else
            (a.1 + 1, a.2.1 + 1, a.2.2.1, a.2.2.2.1, a.2.2.2.2 + 1)) acc
    walkDescend gmap (mirrorAdvance gmap line) (fuel - 1) acc

def reportDescend (path : String) : IO Bool := do
  let gmap ← load_import! path
  let (states, done, bad, good, ungood) :=
    walkDescend gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
  IO.println s!"{path}"
  IO.println s!"  valid states={states}  descents completed={done}"
  IO.println s!"  PickValid violations={bad}"
  IO.println s!"  no-choice endpoints with a VERIFIED chain={good}, without={ungood}"
  if bad == 0 && ungood == 0 then
    IO.println "  both obligations of route A' hold here ✅"
    return true
  else
    IO.println "  route A' obligation BROKEN ❌"
    return false

def runRandomDescend (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- route A' campaign: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut failures := 0
  let mut states := 0
  let mut done := 0
  let mut bad := 0
  let mut good := 0
  let mut ungood := 0
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let (st, dn, bd, gd, ug) := walkDescend gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
    states := states + st; done := done + dn; bad := bad + bd
    good := good + gd; ungood := ungood + ug
    if bd + ug != 0 then
      failures := failures + 1
      IO.FS.writeFile s!"extend_failure_{idx}.cnf" cnf
      IO.println s!"  A' BROKEN at case {idx} (vars={nVars} clauses={nClauses}) \
PickValid={bd} base-case={ug}"
  IO.println s!"--- {cases - failures}/{cases} clean; states={states} descents={done} \
PickValid violations={bad}; no-choice endpoints verified={good} unverified={ungood} ---"
  if failures == 0 then
    IO.println "Every descent completes, and every endpoint carries a verified chain. ✅"
    pure 0
  else
    IO.println s!"{failures} instance(s) break an A' obligation. ❌"
    pure 1

-- ============================================================
-- Probing the ownership relation itself (route to `PairwiseOwned`)
-- ============================================================

/-!
`PairwiseOwned` is the last piece of `ChainSound` that is not plumbing. Two
natural shortcuts to it are worth measuring before either is attempted:

* **symmetry** — if `q` is an owner of `n`, is `n` an owner of `q`?
* **support clique** — are the owners of a single node pairwise co-owned? If
  they were, a chain could be drawn from one node's support and would be
  co-owned for free.

The second is the one that would close it cheaply. The first is a lemma worth
having either way.
-/

/-- Pairs `(n, q)` with `q` an owner of `n` (and a real node) but `n` not an
owner of `q`. -/
def symViolations (g : GPathM) : Nat :=
  g.nodes.foldl (fun acc n =>
    acc + (n.owners.filter (fun q =>
      match g.node? q with
      | some m => !m.owners.contains n.id
      | none => false)).length) 0

/-- Owners of one node, at distinct steps, that do not own each other. Zero
would mean a node's support is a clique — and `PairwiseOwned` would follow for
any chain drawn from it. -/
def cliqueViolations (g : GPathM) : Nat :=
  g.nodes.foldl (fun acc t =>
    acc + t.owners.foldl (fun a q1 =>
      a + (t.owners.filter (fun q2 =>
        (q1.id.step != q2.id.step) &&
        (match g.node? q2 with
         | some m => !m.owners.contains q1
         | none => false))).length) 0) 0

/-- Nodes whose own id is not a global owner. The converse of
`GownersNodes.GownersAreNodes`; `filterRequire` breaks it and `review` is
supposed to restore it. -/
def nodesNotGowners (g : GPathM) : Nat :=
  (g.nodes.filter (fun n => !g.gowners.contains n.id)).length

/-- Nodes that do not own themselves. -/
def notSelfOwned (g : GPathM) : Nat :=
  (g.nodes.filter (fun n => !n.owners.contains n.id)).length

/-- `(states, nodes, symmetry, clique, nodes∉gowners, not self-owned)`. -/
abbrev OAcc := Nat × Nat × Nat × Nat × Nat × Nat

partial def walkOwners (gmap : GMap) (line : MirrorLine) (fuel : Nat)
    (acc : OAcc) : OAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : OAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        (a.1 + 1, a.2.1 + g.nodes.length,
         a.2.2.1 + symViolations g, a.2.2.2.1 + cliqueViolations g,
         a.2.2.2.2.1 + nodesNotGowners g, a.2.2.2.2.2 + notSelfOwned g)) acc
    walkOwners gmap (mirrorAdvance gmap line) (fuel - 1) acc

def reportOwners (path : String) : IO Unit := do
  let gmap ← load_import! path
  let (states, nodes, sym, clique, ng, nso) :=
    walkOwners gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0, 0)
  IO.println s!"{path}"
  IO.println s!"  valid states={states}  nodes={nodes}"
  IO.println s!"  ownership symmetry violations = {sym}"
  IO.println s!"  support-clique violations     = {clique}"
  IO.println s!"  nodes whose id is not a gowner = {ng}"
  IO.println s!"  nodes not owning themselves    = {nso}"

def runRandomOwners (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- ownership relation: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut states := 0
  let mut nodes := 0
  let mut sym := 0
  let mut clique := 0
  let mut symCases := 0
  let mut cliqueCases := 0
  let mut ng := 0
  let mut nso := 0
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let (st, nd, sy, cl, g1, g2) := walkOwners gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0, 0)
    states := states + st; nodes := nodes + nd
    sym := sym + sy; clique := clique + cl
    ng := ng + g1; nso := nso + g2
    if sy != 0 then symCases := symCases + 1
    if cl != 0 then cliqueCases := cliqueCases + 1
  IO.println s!"--- states={states} nodes={nodes} ---"
  IO.println s!"--- symmetry: {sym} violations in {symCases}/{cases} instances ---"
  IO.println s!"--- support clique: {clique} violations in {cliqueCases}/{cases} instances ---"
  IO.println s!"--- nodes not gowners: {ng};  nodes not self-owning: {nso} ---"
  pure 0

-- ============================================================
-- The map-level question: does satisfying the requirements
-- make a path co-owned? (`MapChain.ReqSatImpliesOwned`)
-- ============================================================

def reqOfG (gmap : GMap) (d : NodeId) : List NodeId :=
  match get_node gmap d with
  | some n => n.requires.toList
  | none => []

/-- Every path (parent-linked, one node per step) whose picks satisfy every
requirement of every node on it, up to `cap` of them. -/
partial def collectReqPaths (gmap : GMap) (g : GPathM) (k : Int)
    (chosen : List PathNodeId) (cap : Nat) (acc : List (List PathNodeId)) :
    List (List PathNodeId) :=
  if acc.length ≥ cap then acc
  else if k ≥ g.current_step then acc ++ [chosen.reverse]
  else
    ((g.line k).map (·.id)).foldl (fun a c =>
      if a.length ≥ cap then a
      else
        let linkOk :=
          match chosen with
          | [] => true
          | top :: _ => match g.node? c with
                        | some n => n.parents.contains top
                        | none => false
        let sel := c :: chosen
        let reqOk := (reqOfG gmap c.id).all (fun r =>
          match sel.find? (fun p => p.id.step == r.step) with
          | some p => p.id == r
          | none => true)
        if linkOk && reqOk then collectReqPaths gmap g (k + 1) sel cap a else a) acc

/-- Is a selection pairwise co-owned? -/
def pathCoOwned (g : GPathM) (sel : List PathNodeId) : Bool :=
  sel.all (fun p => sel.all (fun q => p == q || (ownersOfB g q).contains p))

/-- `(states, req-satisfying paths, of those not co-owned, states with NO
req-satisfying path at all)`. That last counter is the open obligation itself:
a valid state the machine holds with no requirement-satisfying path would mean
the machine kept a set it cannot read a solution out of. -/
abbrev RAcc2 := Nat × Nat × Nat × Nat

partial def walkReqPaths (gmap : GMap) (line : MirrorLine) (fuel cap : Nat)
    (acc : RAcc2) : RAcc2 :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : RAcc2) kv =>
      let g := kv.2
      if !isValid g then a else
        let paths := collectReqPaths gmap g 0 [] cap []
        let bad := (paths.filter (fun p => !pathCoOwned g p)).length
        (a.1 + 1, a.2.1 + paths.length, a.2.2.1 + bad,
         a.2.2.2 + (if paths.isEmpty then 1 else 0))) acc
    walkReqPaths gmap (mirrorAdvance gmap line) (fuel - 1) cap acc

def reportReqPaths (path : String) (cap : Nat) : IO Unit := do
  let gmap ← load_import! path
  let (states, paths, bad, none') := walkReqPaths gmap (mirrorInit gmap) 1000 cap (0, 0, 0, 0)
  IO.println s!"{path}"
  IO.println s!"  valid states={states}  requirement-satisfying paths={paths}"
  IO.println s!"  of those, NOT pairwise co-owned = {bad}"
  IO.println s!"  valid states with NO such path  = {none'}"

def runRandomReqPaths (cases seed nvMin nvSpan cap : Nat) : IO UInt32 := do
  IO.println s!"--- ReqSatImpliesOwned: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} cap={cap} ---"
  let mut rng := Rng.ofSeed seed
  let mut states := 0
  let mut paths := 0
  let mut bad := 0
  let mut badCases := 0
  let mut nopath := 0
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let (st, pa, bd, np) := walkReqPaths gmap (mirrorInit gmap) 1000 cap (0, 0, 0, 0)
    states := states + st; paths := paths + pa; bad := bad + bd; nopath := nopath + np
    if bd != 0 then badCases := badCases + 1
  IO.println s!"--- states={states}  requirement-satisfying paths={paths} ---"
  IO.println s!"--- not co-owned: {bad}, in {badCases}/{cases} instances ---"
  IO.println s!"--- valid states with NO requirement-satisfying path: {nopath} ---"
  if bad == 0 then
    IO.println "Every requirement-satisfying path is co-owned. ReqSatImpliesOwned survives. ✅"
  else
    IO.println "ReqSatImpliesOwned is FALSE. ❌"
  pure 0

-- ============================================================
-- The residual gap in `ReqSatImpliesOwned`: map id vs `PathNodeId`
-- ============================================================

/-!
`MapChain.ReqSatisfying` is about **map ids** — `(sel req.step).id = req` — and
lemma L1 pins the owners' map ids at a required step. `PairwiseOwned` is about
**`PathNodeId`s**. So knowing the map id is right does not put the *particular*
path node into the owners list: several `PathNodeId`s can share a map id,
differing in their parent.

That is the whole residual gap for the pinned half of `ReqSatImpliesOwned`, and
it is measurable: at a step some requirement names, how many **distinct
`PathNodeId`s** does a node's owner set hold? If the answer is always one, the
gap closes there.
-/

def distinctPids (l : List PathNodeId) : List PathNodeId :=
  l.foldl (fun acc q => if acc.contains q then acc else acc ++ [q]) []

/-- `(node/requirement pairs looked at, of those with ≥2 distinct owners at the
required step, the largest count seen)`. -/
abbrev PAcc := Nat × Nat × Nat

def pinnedWidth (gmap : GMap) (g : GPathM) : PAcc :=
  g.nodes.foldl (fun (a : PAcc) n =>
    (reqOfG gmap n.id.id).foldl (fun (b : PAcc) r =>
      let os := distinctPids (ownersAt n.owners r.step)
      (b.1 + 1, b.2.1 + (if os.length ≥ 2 then 1 else 0), Nat.max b.2.2 os.length)) a)
    (0, 0, 0)

partial def walkPinned (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : PAcc) : PAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : PAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let p := pinnedWidth gmap g
        (a.1 + p.1, a.2.1 + p.2.1, Nat.max a.2.2 p.2.2)) acc
    walkPinned gmap (mirrorAdvance gmap line) (fuel - 1) acc

def reportPinned (path : String) : IO Unit := do
  let gmap ← load_import! path
  let (pairs, wide, mx) := walkPinned gmap (mirrorInit gmap) 1000 (0, 0, 0)
  IO.println s!"{path}"
  IO.println s!"  (node, requirement) pairs = {pairs}"
  IO.println s!"  with 2+ distinct owner PathNodeIds at the required step = {wide}"
  IO.println s!"  widest owner set at a required step = {mx}"

def runRandomPinned (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- pinned-step width: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut pairs := 0
  let mut wide := 0
  let mut mx := 0
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let (p, w, m) := walkPinned gmap (mirrorInit gmap) 1000 (0, 0, 0)
    pairs := pairs + p; wide := wide + w; mx := Nat.max mx m
  IO.println s!"--- (node, requirement) pairs = {pairs} ---"
  IO.println s!"--- with 2+ distinct owner PathNodeIds at the required step = {wide} ---"
  IO.println s!"--- widest owner set at a required step = {mx} ---"
  pure 0

-- ============================================================
-- The sharpened pinned-step question, restricted to chain nodes
-- ============================================================

/-!
v33 measured owner-set width at pinned steps over **all** nodes, and found sets
of two. That does not settle the question `ReqSatImpliesOwned` actually asks,
which is about nodes **the chain selects**, and which needs only that the
chain's own pick is *in* the set — not that every owner equals it.

So three numbers, over requirement-satisfying paths only:

* how wide the owner set is at a pinned step of a chain node;
* whether the chain's pick is a **member** of it (that is the obligation);
* of the owners there, how many carry `parent_id` equal to the chain's map id
  one step below (the question of whether the parent decides which).
-/

/-- `(chain-node/requirement pairs, sets of width ≥2, chain pick NOT a member,
owners matching the chain's predecessor: none / exactly one / two or more)`. -/
abbrev CAcc := Nat × Nat × Nat × Nat × Nat × Nat

def pinnedOnPath (gmap : GMap) (g : GPathM) (p : List PathNodeId) : CAcc :=
  (List.range p.length).foldl (fun (a : CAcc) j =>
    match p[j]? with
    | none => a
    | some pj =>
      match g.node? pj with
      | none => a
      | some n =>
        (reqOfG gmap pj.id).foldl (fun (b : CAcc) r =>
          let os := distinctPids (ownersAt n.owners r.step)
          let rj := r.step.toNat
          match p[rj]? with
          | none => b
          | some pick =>
            let prev : Option NodeId := if rj = 0 then none else (p[rj - 1]?).map (·.id)
            let nmatch := (os.filter (fun q => q.parent_id == prev)).length
            (b.1 + 1,
             b.2.1 + (if os.length ≥ 2 then 1 else 0),
             b.2.2.1 + (if os.contains pick then 0 else 1),
             b.2.2.2.1 + (if nmatch = 0 then 1 else 0),
             b.2.2.2.2.1 + (if nmatch = 1 then 1 else 0),
             b.2.2.2.2.2 + (if nmatch ≥ 2 then 1 else 0))) a)
    (0, 0, 0, 0, 0, 0)

def addC (a b : CAcc) : CAcc :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1,
   a.2.2.2.2.1 + b.2.2.2.2.1, a.2.2.2.2.2 + b.2.2.2.2.2)

partial def walkPinnedChain (gmap : GMap) (line : MirrorLine) (fuel cap : Nat)
    (acc : CAcc) : CAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : CAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        (collectReqPaths gmap g 0 [] cap []).foldl
          (fun b p => addC b (pinnedOnPath gmap g p)) a) acc
    walkPinnedChain gmap (mirrorAdvance gmap line) (fuel - 1) cap acc

def showC (c : CAcc) : IO Unit := do
  IO.println s!"  (chain node, requirement) pairs = {c.1}"
  IO.println s!"  owner sets of width 2 or more   = {c.2.1}"
  IO.println s!"  chain pick NOT in the owner set = {c.2.2.1}"
  IO.println s!"  owners matching the chain's predecessor: \
none={c.2.2.2.1}  exactly one={c.2.2.2.2.1}  two or more={c.2.2.2.2.2}"

def reportPinnedChain (path : String) (cap : Nat) : IO Unit := do
  let gmap ← load_import! path
  IO.println s!"{path}"
  showC (walkPinnedChain gmap (mirrorInit gmap) 1000 cap (0, 0, 0, 0, 0, 0))

def runRandomPinnedChain (cases seed nvMin nvSpan cap : Nat) : IO UInt32 := do
  IO.println s!"--- pinned steps on chains: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} cap={cap} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : CAcc := (0, 0, 0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    acc := addC acc (walkPinnedChain gmap (mirrorInit gmap) 1000 cap (0, 0, 0, 0, 0, 0))
  showC acc
  pure 0

-- ============================================================
-- The bridge candidates: does the owners ledger contain the
-- structural links?
-- ============================================================

/-!
`OwnerMatchesPredecessor` needs a specific path node to be *in* an owner list.
The owners ledger is built by `addNode` (append `pid` everywhere) and pruned by
`intersectOwners` against `unionOwnersOf`; the parents ledger is built by
`newParents`. Nothing so far connects them.

The minimal candidate bridge is that the two ledgers agree on the direct links:

* **`ParentIsOwner`** — every parent of a node is one of its owners;
* **`SonIsOwner`** — every son of a node is one of its owners.

Both are plausible for a reason worth stating: `upFiltering` filters *before*
it adds, so a node's parents are drawn from an already-filtered line. And the
transitive version (`owns every ancestor`) is *not* plausible — pruning
incompatible ancestors is exactly what the machine is for — which is why the
direct links are the thing to measure.
-/

/-- `(nodes, parent links, parents missing from owners, son links, sons missing
from owners)`. -/
abbrev BAcc := Nat × Nat × Nat × Nat × Nat

def bridgeCount (g : GPathM) : BAcc :=
  g.nodes.foldl (fun (a : BAcc) n =>
    let pm := (n.parents.filter (fun p => !n.owners.contains p)).length
    let sm := (n.sons.filter (fun s => !n.owners.contains s)).length
    (a.1 + 1, a.2.1 + n.parents.length, a.2.2.1 + pm,
     a.2.2.2.1 + n.sons.length, a.2.2.2.2 + sm)) (0, 0, 0, 0, 0)

partial def walkBridge (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : BAcc) : BAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : BAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let b := bridgeCount g
        (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1,
         a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)) acc
    walkBridge gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showB (b : BAcc) : IO Unit := do
  IO.println s!"  nodes={b.1}"
  IO.println s!"  parent links={b.2.1}   parents NOT in owners = {b.2.2.1}"
  IO.println s!"  son links   ={b.2.2.2.1}   sons NOT in owners    = {b.2.2.2.2}"

def reportBridge (path : String) : IO Unit := do
  let gmap ← load_import! path
  IO.println s!"{path}"
  showB (walkBridge gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0))

def runRandomBridge (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- owners/parents bridge: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : BAcc := (0, 0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let b := walkBridge gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
    acc := (acc.1 + b.1, acc.2.1 + b.2.1, acc.2.2.1 + b.2.2.1,
            acc.2.2.2.1 + b.2.2.2.1, acc.2.2.2.2 + b.2.2.2.2)
  showB acc
  pure 0

-- ============================================================
-- Where the two ledgers disagree: on chains, or off them?
-- ============================================================

/-!
The direct-link bridge is **false**, but only just: 37 parent links and 71 son
links out of 328,086 are missing from the owners. So the two ledgers do
disagree, and the parents table is the stale one — ownership pruning never
unlinks a parent, so a node can keep a structural predecessor that propagation
has already ruled out.

The question that decides whether that matters is *where* the disagreement
sits: on the consecutive picks of a requirement-satisfying chain, or only off
them. If only off them, the bridge holds exactly where `OwnerMatchesPredecessor`
needs it — and the stale links are a warning about `PathExists.exists_isChain`,
which descends by picking an arbitrary parent.
-/

/-- `(nodes with a stale parent, consecutive chain pairs, of those not an
ownership link)`. -/
abbrev SAcc := Nat × Nat × Nat

def staleAndChain (gmap : GMap) (g : GPathM) (cap : Nat) : SAcc :=
  let stale := (g.nodes.filter (fun n => n.parents.any (fun p => !n.owners.contains p))).length
  let pairs := (collectReqPaths gmap g 0 [] cap []).foldl (fun (a : Nat × Nat) p =>
    (List.range (p.length - 1)).foldl (fun (b : Nat × Nat) k =>
      match p[k]?, p[k+1]? with
      | some lo, some hi =>
        match g.node? hi with
        | some n => (b.1 + 1, b.2 + (if n.owners.contains lo then 0 else 1))
        | none => b
      | _, _ => b) a) (0, 0)
  (stale, pairs.1, pairs.2)

partial def walkStale (gmap : GMap) (line : MirrorLine) (fuel cap : Nat) (acc : SAcc) : SAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : SAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let b := staleAndChain gmap g cap
        (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)) acc
    walkStale gmap (mirrorAdvance gmap line) (fuel - 1) cap acc

def runRandomStale (cases seed nvMin nvSpan cap : Nat) : IO UInt32 := do
  IO.println s!"--- stale parent links vs chain links: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : SAcc := (0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let b := walkStale gmap (mirrorInit gmap) 1000 cap (0, 0, 0)
    acc := (acc.1 + b.1, acc.2.1 + b.2.1, acc.2.2 + b.2.2)
  IO.println s!"  nodes holding a stale parent (a parent that is not an owner) = {acc.1}"
  IO.println s!"  consecutive pairs on requirement-satisfying chains = {acc.2.1}"
  IO.println s!"  of those, parent NOT an owner = {acc.2.2}"
  pure 0

-- ============================================================
-- Is ownership transitive?
-- ============================================================

/-!
`Bridge.linksInOwners_review` closes the **adjacent** pairs of `PairwiseOwned`
in both directions: on a chain `sel k` is a parent of `sel (k+1)` and
`sel (k+1)` is a son of `sel k`, and every parent and every son is now an
owner. What is left is the non-adjacent pairs — and a single property closes
them all by induction along the chain:

    OwnersTransitive : q ∈ n.owners → r ∈ (node? q).owners → r ∈ n.owners

Walk down from `sel j`: its parent `sel (j-1)` is an owner, the induction
hypothesis puts `sel i` in *that* node's owners, and transitivity carries it
back up. The same argument upward through the sons.

Before the author's fix this was implausible for a stated reason — a node kept
structural predecessors that propagation had already ruled out, so "owns every
ancestor" would have been claiming ownership of pruned-away history. After the
fix the parents table is clean, so the ancestors reachable through it are
exactly the compatible ones. That changes the prior, and makes it worth
measuring.

Two forms are counted, because they are not the same statement:

* **global** — over every node and every owner of it.
* **on the sons/parents link** — the instance the chain induction actually
  uses: `q` a parent (or son) of `n`.
-/

/-- `(pairs checked, violations, link pairs checked, link violations)`. -/
abbrev TAcc := Nat × Nat × Nat × Nat

def transCountNode (g : GPathM) (n : PNodeM) : TAcc :=
  n.owners.foldl (fun (a : TAcc) q =>
    if q == n.id then a else
    match g.node? q with
    | none => a
    | some qn =>
      let isPar := n.parents.contains q
      let isSon := n.sons.contains q
      qn.owners.foldl (fun (b : TAcc) r =>
        let bad := if n.owners.contains r then 0 else 1
        let down := isPar && r.id.step < q.id.step
        let up := isSon && r.id.step > q.id.step
        (b.1 + (if down then 1 else 0), b.2.1 + (if down then bad else 0),
         b.2.2.1 + (if up then 1 else 0), b.2.2.2 + (if up then bad else 0))) a)
    (0, 0, 0, 0)

def transCount (g : GPathM) : TAcc :=
  g.nodes.foldl (fun (a : TAcc) n =>
    let t := transCountNode g n
    (a.1 + t.1, a.2.1 + t.2.1, a.2.2.1 + t.2.2.1, a.2.2.2 + t.2.2.2)) (0, 0, 0, 0)

partial def walkTrans (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : TAcc) : TAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : TAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let t := transCount g
        (a.1 + t.1, a.2.1 + t.2.1, a.2.2.1 + t.2.2.1, a.2.2.2 + t.2.2.2)) acc
    walkTrans gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showT (t : TAcc) : IO Unit := do
  IO.println s!"  DOWN: q a parent of n, r ∈ owners q below q  = {t.1}"
  IO.println s!"          of those, r NOT in owners n          = {t.2.1}"
  IO.println s!"  UP:   q a son of n,    r ∈ owners q above q  = {t.2.2.1}"
  IO.println s!"          of those, r NOT in owners n          = {t.2.2.2}"

def reportTrans (path : String) : IO Unit := do
  let gmap ← load_import! path
  IO.println s!"{path}"
  showT (walkTrans gmap (mirrorInit gmap) 1000 (0, 0, 0, 0))

def runRandomTrans (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- transitivity of ownership: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : TAcc := (0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let t := walkTrans gmap (mirrorInit gmap) 1000 (0, 0, 0, 0)
    acc := (acc.1 + t.1, acc.2.1 + t.2.1, acc.2.2.1 + t.2.2.1, acc.2.2.2 + t.2.2.2)
  showT acc
  pure 0

-- ============================================================
-- Are the pinned states real?
-- ============================================================

/-!
`Pinned.inhabited_of_noChoice` discharges route A′'s base case: a valid state
where propagation has left no choice is inhabited, because `Pinned.pid_unique`
says such a state holds **at most one path node per step**. That is a strong
structural claim, so it is worth checking that it is not vacuous — that the
machine really reaches such states, and that they really collapse.

Counted per valid state: whether `hasChoice` is false, and the largest number
of *distinct* path node ids on any one step. The theorem predicts that number
is 1 whenever the state is `NoChoice`.
-/

/-- `(valid states, of them NoChoice, NoChoice states with some step holding
two distinct ids, largest such width seen)`. -/
abbrev NAcc := Nat × Nat × Nat × Nat

def widestStep (g : GPathM) : Nat :=
  (intRange 0 (g.current_step - 1)).foldl (fun w k =>
    let ids := (g.line k).map (·.id)
    let uniq := ids.foldl (fun (acc : List PathNodeId) i =>
      if acc.contains i then acc else acc ++ [i]) []
    if uniq.length > w then uniq.length else w) 0

partial def walkNoChoice (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : NAcc) : NAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : NAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        if PickInduction.hasChoice g then (a.1 + 1, a.2.1, a.2.2.1, a.2.2.2)
        else
          let w := widestStep g
          (a.1 + 1, a.2.1 + 1, a.2.2.1 + (if w > 1 then 1 else 0),
           if w > a.2.2.2 then w else a.2.2.2)) acc
    walkNoChoice gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showN (t : NAcc) : IO Unit := do
  IO.println s!"  valid states                              = {t.1}"
  IO.println s!"  of those, NoChoice (fully pinned)         = {t.2.1}"
  IO.println s!"  NoChoice states with 2+ ids on some step  = {t.2.2.1}"
  IO.println s!"  widest step seen in a NoChoice state      = {t.2.2.2}"

def runRandomNoChoice (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- pinned (NoChoice) states: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : NAcc := (0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let t := walkNoChoice gmap (mirrorInit gmap) 1000 (0, 0, 0, 0)
    acc := (acc.1 + t.1, acc.2.1 + t.2.1, acc.2.2.1 + t.2.2.1,
            if t.2.2.2 > acc.2.2.2 then t.2.2.2 else acc.2.2.2)
  showN acc
  pure 0

-- ============================================================
-- `PickValid` (∀) against what the descent actually needs (∃)
-- ============================================================

/-!
`PickInduction.Inhabited_of_descent` asks for `PickValid`: **every** map node
the global owners still allow, at **every** step that still has a choice,
propagates to a valid graph. But reading the induction, it consumes exactly
one successful pick per stage — it takes the first `k` with a choice and the
first `q` there only because that is what was convenient to write.

So the honest obligation is the existential one:

    PickSome g : hasChoice g → ∃ k q, q allowed at k, choiceAt g k,
                                      isValid (filterAll g [q.id])

which is what "the machine never has to backtrack" means at its weakest.
This counts both: how many individual picks break validity, and how many
states have **no** good pick at all.
-/

/-- `(states with a choice, states with no good pick, picks, picks that
invalidate)`. -/
abbrev KAcc := Nat × Nat × Nat × Nat × Nat

def pickReport (g : GPathM) : KAcc :=
  let ks := (intRange 0 (g.current_step - 1)).filter (fun k => PickInduction.choiceAt g k)
  if ks.isEmpty then (0, 0, 0, 0, 0)
  else
    let picks := ks.flatMap (fun k => ownersAt g.gowners k)
    let good := picks.filter (fun q => isValid (filterAll g [q.id]))
    let atZero := (picks.filter (fun q => q.id.step == 0)).length
    (1, if good.isEmpty then 1 else 0, picks.length, picks.length - good.length, atZero)

partial def walkPick (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : KAcc) : KAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : KAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let p := pickReport g
        (a.1 + p.1, a.2.1 + p.2.1, a.2.2.1 + p.2.2.1, a.2.2.2.1 + p.2.2.2.1,
         a.2.2.2.2 + p.2.2.2.2)) acc
    walkPick gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showP (t : KAcc) : IO Unit := do
  IO.println s!"  valid states with a choice left           = {t.1}"
  IO.println s!"    of those, NO pick keeps validity (∃)    = {t.2.1}"
  IO.println s!"  individual allowed picks                  = {t.2.2.1}"
  IO.println s!"    of those, pick invalidates (∀)          = {t.2.2.2.1}"
  IO.println s!"  picks at step 0 (outside the threading)    = {t.2.2.2.2}"

def reportPick (path : String) : IO Unit := do
  let gmap ← load_import! path
  IO.println s!"{path}"
  showP (walkPick gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0))

def runRandomPick (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- PickValid (∀) vs PickSome (∃): cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : KAcc := (0, 0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let t := walkPick gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
    acc := (acc.1 + t.1, acc.2.1 + t.2.1, acc.2.2.1 + t.2.2.1, acc.2.2.2.1 + t.2.2.2.1,
            acc.2.2.2.2 + t.2.2.2.2)
  showP acc
  pure 0

-- ============================================================
-- Which sweep of the review carries the risk in `PickValid`?
-- ============================================================

/-!
`filterAll g [mid] = review (filterRequire g mid)`, and `review` is a fuel loop
over `reviewPass = reviewSons ∘ reviewParents ∘ cleanInvalid`. The pin itself
is harmless (`isValid_filterRequire`), so the whole of `PickValid` sits in
those three sweeps — but not necessarily evenly.

`cleanInvalid` is the sweep that *does* the pinning work: it intersects every
node's owners with the narrowed global owners and drops whoever is left
unsupported. The two coherence sweeps re-check against neighbours. If they
remove nothing after a pin, then `PickValid` is a theorem about `cleanInvalid`
alone — which is the sweep the arc-consistency clauses speak about.

Counted per allowed pick: nodes before, after `cleanInvalid`, after the full
`review`; and whether each stage is still valid.
-/

/-- `(picks, cleanInvalid invalid, review invalid, picks where review removes
strictly more than cleanInvalid, total extra nodes removed by the coherence
sweeps)`. -/
abbrev VAcc := Nat × Nat × Nat × Nat × Nat

def sweepReport (g : GPathM) : VAcc :=
  let ks := (intRange 0 (g.current_step - 1)).filter (fun k => PickInduction.choiceAt g k)
  (ks.flatMap (fun k => ownersAt g.gowners k)).foldl (fun (a : VAcc) q =>
    let g' := filterRequire g q.id
    let c := cleanInvalid g'
    let r := review g'
    let extra := c.nodes.length - r.nodes.length
    (a.1 + 1,
     a.2.1 + (if isValid c then 0 else 1),
     a.2.2.1 + (if isValid r then 0 else 1),
     a.2.2.2.1 + (if extra > 0 then 1 else 0),
     a.2.2.2.2 + extra)) (0, 0, 0, 0, 0)

partial def walkSweep (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : VAcc) : VAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : VAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let v := sweepReport g
        (a.1 + v.1, a.2.1 + v.2.1, a.2.2.1 + v.2.2.1,
         a.2.2.2.1 + v.2.2.2.1, a.2.2.2.2 + v.2.2.2.2)) acc
    walkSweep gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showV (t : VAcc) : IO Unit := do
  IO.println s!"  allowed picks                              = {t.1}"
  IO.println s!"    cleanInvalid alone leaves it INVALID     = {t.2.1}"
  IO.println s!"    full review leaves it INVALID            = {t.2.2.1}"
  IO.println s!"  picks where the coherence sweeps remove more = {t.2.2.2.1}"
  IO.println s!"    total extra nodes they remove            = {t.2.2.2.2}"

def runRandomSweep (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- which sweep carries PickValid: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : VAcc := (0, 0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let v := walkSweep gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
    acc := (acc.1 + v.1, acc.2.1 + v.2.1, acc.2.2.1 + v.2.2.1,
            acc.2.2.2.1 + v.2.2.2.1, acc.2.2.2.2 + v.2.2.2.2)
  showV acc
  pure 0

-- ============================================================
-- Is the pinned set self-supporting?
-- ============================================================

/-!
`Survive.isValid_cleanInvalid_of_Closed` proves that a **self-supporting set**
cannot be removed by `cleanInvalid`. For the pin at step `k` to map id `mid`,
the natural candidate is

    S = { n : n owns, at step k, a path node whose map id is mid }

which is exactly what `cleanInvalid` is trying to keep. Four of `Closed`'s six
clauses are free (`gow`, `node`, `parent`, `coown`). This counts the other two:

* **support** — every member has, at every step, an owner that is a member.
  This is the mathematical residue, and it *is* `PickValid` without chains.
* **son** — every non-top member is the parent of a member. Free from
  `coherent_sons` except that turning a son link round needs the mirror
  `Sons.SMP` does not have, so it is counted too.
-/

abbrev XAcc := Nat × Nat × Nat × Nat

def inSid (g : GPathM) (k : Int) (mid : NodeId) (v : PathNodeId) : Bool :=
  match g.node? v with
  | some m => (ownersAt m.owners k).any (fun u => u.id == mid)
  | none => false

def closedReport (g : GPathM) : XAcc :=
  let ks := (intRange 0 (g.current_step - 1)).filter (fun k => PickInduction.choiceAt g k)
  let picks := ks.flatMap (fun k => (ownersAt g.gowners k).map (fun q => (k, q.id)))
  picks.foldl (fun (a : XAcc) kq =>
    let k := kq.1
    let mid := kq.2
    let mem := g.nodes.filter (fun n => (ownersAt n.owners k).any (fun u => u.id == mid))
    mem.foldl (fun (b : XAcc) n =>
      let sup := (intRange 0 (g.current_step - 1)).foldl (fun (c : Nat × Nat) l =>
        let far := l != k && l != n.id.id.step
          && l != n.id.id.step - 1 && l != n.id.id.step + 1
        if !far then c
        else if (ownersAt n.owners l).any (fun v => inSid g k mid v)
        then (c.1 + 1, c.2) else (c.1 + 1, c.2 + 1)) (0, 0)
      let sonOk := n.id.id.step == g.current_step - 1 ||
        mem.any (fun c => c.parents.contains n.id)
      (b.1 + sup.1, b.2.1 + sup.2, b.2.2.1 + 1,
       b.2.2.2 + (if sonOk then 0 else 1))) a) (0, 0, 0, 0)

partial def walkClosed (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : XAcc) : XAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : XAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let x := closedReport g
        (a.1 + x.1, a.2.1 + x.2.1, a.2.2.1 + x.2.2.1, a.2.2.2 + x.2.2.2)) acc
    walkClosed gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showX (t : XAcc) : IO Unit := do
  IO.println s!"  FAR support checks (|l-step|>1, l != pin) = {t.1}"
  IO.println s!"    no member owned there                   = {t.2.1}"
  IO.println s!"  son checks (non-top member)               = {t.2.2.1}"
  IO.println s!"    not the parent of any member            = {t.2.2.2}"

def runRandomClosed (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- is the pinned set self-supporting: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : XAcc := (0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let x := walkClosed gmap (mirrorInit gmap) 1000 (0, 0, 0, 0)
    acc := (acc.1 + x.1, acc.2.1 + x.2.1, acc.2.2.1 + x.2.2.1, acc.2.2.2 + x.2.2.2)
  showX acc
  pure 0

-- ============================================================
-- Does the arc-consistent core reach every step?
-- ============================================================

/-!
`Survive.Closed_Core` removes `support` from the account: the union of every
self-supporting set is self-supporting, so the clauses hold of the **core** by
construction. What is left of `cleanInvalid` after a pin is one statement —
*the core reaches every step*.

This computes the core directly, by narrowing `gowners` under the `Closed`
clauses until it stops shrinking, and asks whether every step survives. It is
deliberately **not** `review`: it never calls `isValidNode`, only the clauses
of `Closed`, so a clean result is not a restatement of the pruning's own
verdict.
-/

abbrev CoAcc := Nat × Nat × Nat × Nat

def coreStep (g : GPathM) (S : List PathNodeId) : List PathNodeId :=
  S.filter (fun p =>
    match g.node? p with
    | none => false
    | some n =>
      (intRange 0 (g.current_step - 1)).all (fun l =>
        (ownersAt n.owners l).any (fun v => S.contains v))
      && (p.parent_id.isNone || n.parents.any (fun c => S.contains c))
      && (p.id.step == g.current_step - 1
          || S.any (fun c => match g.node? c with
                             | some m => m.parents.contains p
                             | none => false)))

partial def coreFix (g : GPathM) (S : List PathNodeId) (fuel : Nat) : List PathNodeId :=
  if fuel = 0 then S
  else
    let S' := coreStep g S
    if S'.length == S.length then S else coreFix g S' (fuel - 1)

def coreReport (g : GPathM) : CoAcc :=
  let ks := (intRange 0 (g.current_step - 1)).filter (fun k => PickInduction.choiceAt g k)
  let picks := ks.flatMap (fun k => ownersAt g.gowners k)
  picks.foldl (fun (a : CoAcc) q =>
    let g' := filterRequire g q.id
    let core := coreFix g' g'.gowners 200
    let missing := ((intRange 0 (g'.current_step - 1)).filter
      (fun l => !core.any (fun p => p.id.step == l))).length
    (a.1 + 1, a.2.1 + (if missing > 0 then 1 else 0), a.2.2.1 + missing,
     a.2.2.2 + core.length)) (0, 0, 0, 0)

partial def walkCore (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : CoAcc) : CoAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : CoAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let c := coreReport g
        (a.1 + c.1, a.2.1 + c.2.1, a.2.2.1 + c.2.2.1, a.2.2.2 + c.2.2.2)) acc
    walkCore gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showCo (t : CoAcc) : IO Unit := do
  IO.println s!"  pins examined                             = {t.1}"
  IO.println s!"    core misses at least one step           = {t.2.1}"
  IO.println s!"    total (pin, step) pairs left empty      = {t.2.2.1}"
  IO.println s!"  total core size over all pins             = {t.2.2.2}"

def runRandomCore (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- does the arc-consistent core reach every step: cases={cases} \
seed={seed} vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : CoAcc := (0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let c := walkCore gmap (mirrorInit gmap) 1000 (0, 0, 0, 0)
    acc := (acc.1 + c.1, acc.2.1 + c.2.1, acc.2.2.1 + c.2.2.1, acc.2.2.2 + c.2.2.2)
  showCo acc
  pure 0

-- ============================================================
-- Is the candidate set closed downward under ownership?
-- ============================================================

/-!
`support` at distance ≥ 2 asks a candidate for **some** candidate owner at a
far step. A strictly stronger statement would make it trivial:

    every owner of a candidate is a candidate

because `owners_ok` already hands out an owner at every step. Whether that
holds is a closure question, not an existence question, and closure questions
are the kind that induct. So it is worth knowing before trying to prove
anything.

(The neighbouring statement — every owner of a candidate is *compatible with*
the candidate's own pinned owner — is the support clique, refuted in v28 with
63.9M violations. This one is weaker: it only asks the owner to own *some*
node with the pinned map id.)
-/

abbrev DAcc2 := Nat × Nat × Nat × Nat

def isCand (_g : GPathM) (k : Int) (mid : NodeId) (n : PNodeM) : Bool :=
  (ownersAt n.owners k).any (fun u => u.id == mid)

def downReport (g : GPathM) : DAcc2 :=
  let ks := (intRange 0 (g.current_step - 1)).filter (fun k => PickInduction.choiceAt g k)
  let picks := ks.flatMap (fun k => (ownersAt g.gowners k).map (fun q => (k, q.id)))
  picks.foldl (fun (a : DAcc2) kq =>
    let k := kq.1
    let mid := kq.2
    let mem := g.nodes.filter (fun n => isCand g k mid n)
    mem.foldl (fun (b : DAcc2) n =>
      n.owners.foldl (fun (c : DAcc2) v =>
        if v.id.step < 0 || v.id.step >= g.current_step then c
        else
          let far := v.id.step != k && v.id.step != n.id.id.step
            && v.id.step != n.id.id.step - 1 && v.id.step != n.id.id.step + 1
          let ok := match g.node? v with
                    | some m => isCand g k mid m
                    | none => false
          (c.1 + 1, c.2.1 + (if ok then 0 else 1),
           c.2.2.1 + (if far then 1 else 0),
           c.2.2.2 + (if far && !ok then 1 else 0))) b) a) (0, 0, 0, 0)

partial def walkDown (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : DAcc2) : DAcc2 :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : DAcc2) kv =>
      let g := kv.2
      if !isValid g then a else
        let d := downReport g
        (a.1 + d.1, a.2.1 + d.2.1, a.2.2.1 + d.2.2.1, a.2.2.2 + d.2.2.2)) acc
    walkDown gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showD2 (t : DAcc2) : IO Unit := do
  IO.println s!"  (candidate, owner) pairs                  = {t.1}"
  IO.println s!"    owner is NOT a candidate                = {t.2.1}"
  IO.println s!"  of those, owner at a far step             = {t.2.2.1}"
  IO.println s!"    far owner is NOT a candidate            = {t.2.2.2}"

def runRandomDown (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- is the candidate set downward closed: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : DAcc2 := (0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let d := walkDown gmap (mirrorInit gmap) 1000 (0, 0, 0, 0)
    acc := (acc.1 + d.1, acc.2.1 + d.2.1, acc.2.2.1 + d.2.2.1, acc.2.2.2 + d.2.2.2)
  showD2 acc
  pure 0

-- ============================================================
-- Does the anchored descent stay inside the node's own support?
-- ============================================================

/-!
The candidate set is **not** downward closed (measured: 722,851 of 3,723,185
owner pairs), so `support`'s existential is doing real work: a candidate has
*some* candidate owner at a far step, not all of them.

`Threaded.hop_down` builds the obvious witness — descend from `p` picking, at
each step, a parent that still owns the pinned node `u`. Every node of that
descent is a candidate by construction. The only thing missing is whether it
stays inside **`p`'s own owners**: the bridge gives the first hop for free
(a parent is an owner), and v40 refuted the second (a grandparent need not be).

So this counts, along the anchored descent from each candidate: how often a
descent node is not an owner of the node it started from — and, when the
first-parent choice fails, whether *some* parent choice would have worked.
-/

abbrev EAcc := Nat × Nat × Nat × Nat

/-- The first parent of `d` that still owns `u`, if any. -/
def descendStep (g : GPathM) (u : PathNodeId) (d : PNodeM) : Option PNodeM :=
  (d.parents.findSome? (fun c =>
    match g.node? c with
    | some m => if m.owners.contains u then some m else none
    | none => none))

partial def descendWalk (g : GPathM) (u : PathNodeId) (top : PNodeM) (d : PNodeM)
    (fuel : Nat) (acc : Nat × Nat) : Nat × Nat :=
  if fuel = 0 then acc
  else
    match descendStep g u d with
    | none => acc
    | some m =>
      let bad := if top.owners.contains m.id then 0 else 1
      descendWalk g u top m (fuel - 1) (acc.1 + 1, acc.2 + bad)

def descReport (g : GPathM) : EAcc :=
  let ks := (intRange 0 (g.current_step - 1)).filter (fun k => PickInduction.choiceAt g k)
  let picks := ks.flatMap (fun k => (ownersAt g.gowners k).map (fun q => (k, q.id)))
  picks.foldl (fun (a : EAcc) kq =>
    let k := kq.1
    let mid := kq.2
    let mem := g.nodes.filter (fun n => isCand g k mid n)
    mem.foldl (fun (b : EAcc) n =>
      match (ownersAt n.owners k).find? (fun u => u.id == mid) with
      | none => b
      | some u =>
        let r := descendWalk g u n n 60 (0, 0)
        (b.1 + 1, b.2.1 + (if r.2 > 0 then 1 else 0), b.2.2.1 + r.1, b.2.2.2 + r.2)) a)
    (0, 0, 0, 0)

partial def walkDesc (gmap : GMap) (line : MirrorLine) (fuel : Nat) (acc : EAcc) : EAcc :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : EAcc) kv =>
      let g := kv.2
      if !isValid g then a else
        let d := descReport g
        (a.1 + d.1, a.2.1 + d.2.1, a.2.2.1 + d.2.2.1, a.2.2.2 + d.2.2.2)) acc
    walkDesc gmap (mirrorAdvance gmap line) (fuel - 1) acc

def showE (t : EAcc) : IO Unit := do
  IO.println s!"  anchored descents run                     = {t.1}"
  IO.println s!"    descents leaving the start's support    = {t.2.1}"
  IO.println s!"  descent hops taken                        = {t.2.2.1}"
  IO.println s!"    hop lands outside the start's support   = {t.2.2.2}"

def runRandomDesc (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- does the anchored descent stay in the support: cases={cases} \
seed={seed} vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acc : EAcc := (0, 0, 0, 0)
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
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "extend_tmp.cnf" cnf
    let gmap ← load_import! "extend_tmp.cnf"
    let d := walkDesc gmap (mirrorInit gmap) 1000 (0, 0, 0, 0)
    acc := (acc.1 + d.1, acc.2.1 + d.2.1, acc.2.2.1 + d.2.2.1, acc.2.2.2 + d.2.2.2)
  showE acc
  pure 0

end AbsSat.GraphPath.Model.ExtendSearch
