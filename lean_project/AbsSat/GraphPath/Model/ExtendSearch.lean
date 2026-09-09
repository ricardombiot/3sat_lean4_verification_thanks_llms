-- lean_project/AbsSat/GraphPath/Model/ExtendSearch.lean
import AbsSat.GraphPath.Model.Extendable
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

end AbsSat.GraphPath.Model.ExtendSearch
