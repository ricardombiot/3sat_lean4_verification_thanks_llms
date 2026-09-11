-- lean_project/AbsSat/GraphMap/SymCampaign.lean
import AbsSat.GraphMap.CnfMapDiff
import AbsSat.GraphPath.Model.SymReview
import AbsSat.GraphPath.Model.TriReview
import AbsSat.GraphMap.CnfHypergraph
import AbsSat.GraphMap.CnfReducer
import AbsSat.GraphMap.CnfSelection

/-!
`lake exe cnfmap --symreview`: the original machine against the symmetric one
(`SymReview`), on the same formulas, with brute force as the oracle.

Validation infrastructure: `IO` and `partial`, no theorems, no pins.
-/

namespace AbsSat.GraphMap.SymCampaign

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapDiff
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.SymReview

-- ------------------------------------------------------------
-- The symmetric machine: the pure driver with `upFilteringSym`
-- ------------------------------------------------------------

def sendToSym (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  let g' := upFilteringSym g (reqOfCnf φ d) d ""
  if isValid g' then insertPure next d g' else next

def sendAllSym (φ : Cnf) (kv : NodeId × GPathM) (next : PureLine) : PureLine :=
  (mapSons φ kv.1.step kv.1.index).foldl (sendToSym φ kv.2) next

def pureAdvanceSym (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv => sendAllSym φ kv next) []

-- ------------------------------------------------------------
-- Measures
-- ------------------------------------------------------------

def symViol (g : GPathM) : Nat :=
  g.nodes.foldl (fun acc n =>
    acc + (n.owners.filter (fun q =>
      match g.node? q with
      | some m => !m.owners.contains n.id
      | none => false)).length) 0

def firstChoiceC (g : GPathM) : Option PathNodeId :=
  (intRange 0 (g.current_step - 1)).findSome? (fun k =>
    if PickInduction.choiceAt g k then (ownersAt g.gowners k).head? else none)

/-- The assignment a no-choice state reads off: the surviving map node at each
variable's positive step. -/
def readAssign (g : GPathM) : Assign := fun v =>
  match (ownersAt g.gowners (2 * (v : Int))).head? with
  | some q => q.id.index == 1
  | none => false

/-- The step-pin reader (`filterAll` on one map id), as `ExtendSearch.descend`. -/
partial def readStep (g : GPathM) (fuel : Nat) : Option GPathM :=
  if fuel = 0 then none
  else if !PickInduction.hasChoice g then some g
  else match firstChoiceC g with
    | none => some g
    | some r =>
      let g' := filterAll g [r.id]
      if isValid g' then readStep g' (fuel - 1) else none

/-- The owners-pin reader over the symmetric review; also sums the symmetry
violations of every state it passes through. -/
partial def readOwners (g : GPathM) (fuel : Nat) (sv : Nat) : Option (GPathM × Nat) :=
  if fuel = 0 then none
  else if !PickInduction.hasChoice g then some (g, sv)
  else match firstChoiceC g with
    | none => some (g, sv)
    | some r =>
      let g' := readStepSym g r
      if isValid g' then readOwners g' (fuel - 1) (sv + symViol g') else none

/-- `PickValid`, both ways: over every global owner at a step with a choice,
does the pin leave the graph valid? `(picks, step-pin failures, owners-pin
failures)`. -/
def pickValidAll (g : GPathM) : Nat × Nat × Nat :=
  (intRange 0 (g.current_step - 1)).foldl (fun acc k =>
    if !PickInduction.choiceAt g k then acc else
    (ownersAt g.gowners k).foldl (fun (a : Nat × Nat × Nat) r =>
      (a.1 + 1,
       a.2.1 + (if isValid (filterAll g [r.id]) then 0 else 1),
       a.2.2 + (if isValid (readStepSym g r) then 0 else 1))) acc) (0, 0, 0)

structure SAcc where
  inst : Nat := 0
  satTruth : Nat := 0
  origSat : Nat := 0
  symSat : Nat := 0
  origUnsound : Nat := 0
  symUnsound : Nat := 0
  origZombie : Nat := 0
  symZombie : Nat := 0
  origStates : Nat := 0
  symStates : Nat := 0
  origNodes : Nat := 0
  symNodes : Nat := 0
  origSymViol : Nat := 0
  symSymViol : Nat := 0
  -- reads from the final states of each machine
  origFinals : Nat := 0
  symFinals : Nat := 0
  readStepOk : Nat := 0
  readStepCert : Nat := 0
  readOwnOk : Nat := 0
  readOwnCert : Nat := 0
  readOwnSymViol : Nat := 0
  picks : Nat := 0
  pickStepFail : Nat := 0
  pickOwnFail : Nat := 0
  symPicks : Nat := 0
  symPickOwnFail : Nat := 0
  symReadOk : Nat := 0
  symReadCert : Nat := 0

def addS (a b : SAcc) : SAcc :=
  { inst := a.inst + b.inst, satTruth := a.satTruth + b.satTruth,
    origSat := a.origSat + b.origSat, symSat := a.symSat + b.symSat,
    origUnsound := a.origUnsound + b.origUnsound, symUnsound := a.symUnsound + b.symUnsound,
    origZombie := a.origZombie + b.origZombie, symZombie := a.symZombie + b.symZombie,
    origStates := a.origStates + b.origStates, symStates := a.symStates + b.symStates,
    origNodes := a.origNodes + b.origNodes, symNodes := a.symNodes + b.symNodes,
    origSymViol := a.origSymViol + b.origSymViol, symSymViol := a.symSymViol + b.symSymViol,
    origFinals := a.origFinals + b.origFinals, symFinals := a.symFinals + b.symFinals,
    readStepOk := a.readStepOk + b.readStepOk, readStepCert := a.readStepCert + b.readStepCert,
    readOwnOk := a.readOwnOk + b.readOwnOk, readOwnCert := a.readOwnCert + b.readOwnCert,
    readOwnSymViol := a.readOwnSymViol + b.readOwnSymViol,
    picks := a.picks + b.picks, pickStepFail := a.pickStepFail + b.pickStepFail,
    pickOwnFail := a.pickOwnFail + b.pickOwnFail,
    symPicks := a.symPicks + b.symPicks, symPickOwnFail := a.symPickOwnFail + b.symPickOwnFail,
    symReadOk := a.symReadOk + b.symReadOk, symReadCert := a.symReadCert + b.symReadCert }

def bruteSat (φ : Cnf) : Bool :=
  (List.range (Nat.pow 2 φ.nVars)).any (fun m => satB (assignOfNat m) φ)

def symReport (φ : Cnf) : SAcc := Id.run do
  let truth := bruteSat φ
  let steps := (stepCount φ - 1).toNat
  let mut acc : SAcc := { inst := 1, satTruth := if truth then 1 else 0 }
  -- original machine
  let mut line := pureInit φ
  for _ in [0:steps] do
    for kv in line do
      acc := { acc with origStates := acc.origStates + 1,
                        origNodes := acc.origNodes + kv.2.nodes.length,
                        origSymViol := acc.origSymViol + symViol kv.2 }
    line := pureAdvance φ line
  let finals0 := line.filter (fun kv => isValid kv.2)
  -- symmetric machine
  let mut lineS := pureInit φ
  for _ in [0:steps] do
    for kv in lineS do
      acc := { acc with symStates := acc.symStates + 1,
                        symNodes := acc.symNodes + kv.2.nodes.length,
                        symSymViol := acc.symSymViol + symViol kv.2 }
    lineS := pureAdvanceSym φ lineS
  let finals1 := lineS.filter (fun kv => isValid kv.2)
  for kv in finals0 do
    acc := { acc with origStates := acc.origStates + 1,
                      origNodes := acc.origNodes + kv.2.nodes.length,
                      origSymViol := acc.origSymViol + symViol kv.2 }
  for kv in finals1 do
    acc := { acc with symStates := acc.symStates + 1,
                      symNodes := acc.symNodes + kv.2.nodes.length,
                      symSymViol := acc.symSymViol + symViol kv.2 }
  let v0 := !finals0.isEmpty
  let v1 := !finals1.isEmpty
  acc := { acc with origSat := if v0 then 1 else 0, symSat := if v1 then 1 else 0,
                    origUnsound := if truth && !v0 then 1 else 0,
                    symUnsound := if truth && !v1 then 1 else 0,
                    origZombie := if !truth && v0 then 1 else 0,
                    symZombie := if !truth && v1 then 1 else 0 }
  -- reads from the original machine's final states
  for kv in finals0 do
    let g := kv.2
    let pv := pickValidAll g
    acc := { acc with origFinals := acc.origFinals + 1, picks := acc.picks + pv.1,
                      pickStepFail := acc.pickStepFail + pv.2.1,
                      pickOwnFail := acc.pickOwnFail + pv.2.2 }
    match readStep g 10000 with
    | some ge =>
      acc := { acc with readStepOk := acc.readStepOk + 1,
                        readStepCert := acc.readStepCert + (if satB (readAssign ge) φ then 1 else 0) }
    | none => pure ()
    match readOwners g 10000 0 with
    | some (ge, sv) =>
      acc := { acc with readOwnOk := acc.readOwnOk + 1, readOwnSymViol := acc.readOwnSymViol + sv,
                        readOwnCert := acc.readOwnCert + (if satB (readAssign ge) φ then 1 else 0) }
    | none => pure ()
  -- reads from the symmetric machine's final states
  for kv in finals1 do
    let g := kv.2
    let pv := pickValidAll g
    acc := { acc with symFinals := acc.symFinals + 1, symPicks := acc.symPicks + pv.1,
                      symPickOwnFail := acc.symPickOwnFail + pv.2.2 }
    match readOwners g 10000 0 with
    | some (ge, sv) =>
      acc := { acc with symReadOk := acc.symReadOk + 1, readOwnSymViol := acc.readOwnSymViol + sv,
                        symReadCert := acc.symReadCert + (if satB (readAssign ge) φ then 1 else 0) }
    | none => pure ()
  return acc

def runSymReview (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- original vs symmetric review: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : SAcc := {}
  let mut skipped := 0
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => skipped := skipped + 1
    | .ok φ =>
      if !AbsSat.Cnf.Dimacs.wfB φ then skipped := skipped + 1
      else acc := addS acc (symReport φ)
  IO.println s!"  instances (skipped non-WF)                = {acc.inst} ({skipped})"
  IO.println s!"  satisfiable by brute force                = {acc.satTruth}"
  IO.println s!"  --- verdicts ---"
  IO.println s!"  original says SAT / symmetric says SAT    = {acc.origSat} / {acc.symSat}"
  IO.println s!"  LOST A SOLUTION  original / symmetric     = {acc.origUnsound} / {acc.symUnsound}"
  IO.println s!"  ZOMBIE VERDICT   original / symmetric     = {acc.origZombie} / {acc.symZombie}"
  IO.println s!"  --- the run ---"
  IO.println s!"  states   original / symmetric             = {acc.origStates} / {acc.symStates}"
  IO.println s!"  nodes    original / symmetric             = {acc.origNodes} / {acc.symNodes}"
  IO.println s!"  SYMMETRY VIOLATIONS original / symmetric  = {acc.origSymViol} / {acc.symSymViol}"
  IO.println s!"  --- reading the original machine's final states ({acc.origFinals}) ---"
  IO.println s!"  picks tested (PickValid, every choice)    = {acc.picks}"
  IO.println s!"    step-pin + review   failures            = {acc.pickStepFail}"
  IO.println s!"    owners-pin + symmetric review failures  = {acc.pickOwnFail}"
  IO.println s!"  step-pin reader    finished / certified   = {acc.readStepOk} / {acc.readStepCert}"
  IO.println s!"  owners-pin reader  finished / certified   = {acc.readOwnOk} / {acc.readOwnCert}"
  IO.println s!"  --- reading the symmetric machine's final states ({acc.symFinals}) ---"
  IO.println s!"  picks tested                              = {acc.symPicks}"
  IO.println s!"    owners-pin + symmetric review failures  = {acc.symPickOwnFail}"
  IO.println s!"  owners-pin reader  finished / certified   = {acc.symReadOk} / {acc.symReadCert}"
  IO.println s!"  symmetry violations along owners-pin reads = {acc.readOwnSymViol}"
  pure 0


-- ------------------------------------------------------------
-- Path consistency ("triangle") at a symmetric fixpoint
-- ------------------------------------------------------------

/-- For every co-owned pair `(p, r)` at distinct steps: is there, at every step,
a node owned by both? `(pairs, pairs with a gap)`. -/
def triangle (g : GPathM) : Nat × Nat :=
  g.nodes.foldl (fun acc p =>
    p.owners.foldl (fun (a : Nat × Nat) rid =>
      if rid.id.step ≤ p.id.id.step then a else
      match g.node? rid with
      | none => a
      | some r =>
        if !r.owners.contains p.id then a else
        let inter := p.owners.filter (fun q => r.owners.contains q)
        let gap := (intRange 0 (g.current_step - 1)).any (fun k =>
          !(inter.any (fun q => q.id.step == k)))
        (a.1 + 1, a.2 + (if gap then 1 else 0))) acc) (0, 0)

def runTriangle (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- path consistency at symmetric fixpoints: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut finals := 0
  let mut pairs := 0
  let mut gaps := 0
  let mut rstates := 0
  let mut rpairs := 0
  let mut rgaps := 0
  let mut istates := 0
  let mut ipairs := 0
  let mut igaps := 0
  let mut ostates := 0
  let mut opairs := 0
  let mut ogaps := 0
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let steps := (stepCount φ - 1).toNat
        let mut line := pureInit φ
        for _ in [0:steps] do
          for kv in line do
            if isValid kv.2 then
              istates := istates + 1
              let t := triangle kv.2
              ipairs := ipairs + t.1
              igaps := igaps + t.2
          line := pureAdvanceSym φ line
        let mut lineO := pureInit φ
        for _ in [0:steps] do
          lineO := pureAdvance φ lineO
          for kv in lineO do
            if isValid kv.2 then
              ostates := ostates + 1
              let t := triangle kv.2
              opairs := opairs + t.1
              ogaps := ogaps + t.2
        for kv in line do
          if isValid kv.2 then
            finals := finals + 1
            let t := triangle kv.2
            pairs := pairs + t.1
            gaps := gaps + t.2
            -- walk the owners-pin read, measuring every state on the way
            let mut g := kv.2
            let mut fuel := 200
            while fuel > 0 && PickInduction.hasChoice g do
              fuel := fuel - 1
              match firstChoiceC g with
              | none => fuel := 0
              | some r =>
                g := readStepSym g r
                if isValid g then
                  rstates := rstates + 1
                  let t := triangle g
                  rpairs := rpairs + t.1
                  rgaps := rgaps + t.2
                else fuel := 0
  IO.println s!"  ORIGINAL machine, all valid states        = {ostates}"
  IO.println s!"  co-owned pairs there                      = {opairs}"
  IO.println s!"    with a gap                              = {ogaps}"
  IO.println s!"  symmetric machine, intermediate states    = {istates}"
  IO.println s!"  co-owned pairs there                      = {ipairs}"
  IO.println s!"    with a gap                              = {igaps}"
  IO.println s!"  final valid states (symmetric machine)    = {finals}"
  IO.println s!"  co-owned pairs                            = {pairs}"
  IO.println s!"    with a step no common owner covers      = {gaps}"
  IO.println s!"  states along owners-pin reads             = {rstates}"
  IO.println s!"  co-owned pairs there                      = {rpairs}"
  IO.println s!"    with a gap                              = {rgaps}"
  pure 0


-- ------------------------------------------------------------
-- Is choosing `r` exactly keeping `owners(r)`?
-- ------------------------------------------------------------

/-- For every choice `r` at a step with a choice: the nodes among `owners(r)`,
how many of them the read step kills, and how many survivors lie outside
`owners(r)`. `(picks, owner-nodes, killed, outside)`. -/
def pinExact (g : GPathM) : Nat × Nat × Nat × Nat :=
  (intRange 0 (g.current_step - 1)).foldl (fun acc k =>
    if !PickInduction.choiceAt g k then acc else
    (ownersAt g.gowners k).foldl (fun (a : Nat × Nat × Nat × Nat) r =>
      match g.node? r with
      | none => a
      | some rn =>
        let g' := readStepSym g r
        let ownNodes := g.nodes.filter (fun n => rn.owners.contains n.id)
        let killed := (ownNodes.filter (fun n => (g'.node? n.id).isNone)).length
        let outside := (g'.nodes.filter (fun n => !rn.owners.contains n.id)).length
        (a.1 + 1, a.2.1 + ownNodes.length, a.2.2.1 + killed, a.2.2.2 + outside)) acc)
    (0, 0, 0, 0)

def runPinExact (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- choosing r = keeping owners(r)? cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut states := 0
  let mut acc : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let steps := (stepCount φ - 1).toNat
        let mut line := pureInit φ
        for _ in [0:steps] do
          line := pureAdvanceSym φ line
        for kv in line do
          if isValid kv.2 then
            -- the final state and every state of its owners-pin read
            let mut g := kv.2
            let mut fuel := 200
            let mut go := true
            while go do
              states := states + 1
              let t := pinExact g
              acc := (acc.1 + t.1, acc.2.1 + t.2.1, acc.2.2.1 + t.2.2.1, acc.2.2.2 + t.2.2.2)
              fuel := fuel - 1
              if fuel == 0 || !PickInduction.hasChoice g then go := false
              else
                match firstChoiceC g with
                | none => go := false
                | some r =>
                  g := readStepSym g r
                  if !isValid g then go := false
  IO.println s!"  full-length states examined               = {states}"
  IO.println s!"  choices tried                             = {acc.1}"
  IO.println s!"  nodes among the chosen node's owners      = {acc.2.1}"
  IO.println s!"    KILLED by choosing it                   = {acc.2.2.1}"
  IO.println s!"  survivors OUTSIDE the chosen node's owners = {acc.2.2.2}"
  pure 0


-- ------------------------------------------------------------
-- Is owners(r) self-supporting?
-- ------------------------------------------------------------

/-- For `S = owners(r)` and each node `p ∈ S`, with `T(p) = owners(p) ∩ S`:
(b) `p` has a parent in `T(p)` (unless at step 0) and a son in `T(p)` (unless at
the top); (c) every `q ∈ T(p)` is owned by some parent of `p` in `T(p)`, and by
some son of `p` in `T(p)`. `(nodes checked, (b) failures, (c) failures)`. -/
def selfSupport (g : GPathM) (rn : PNodeM) : Nat × Nat × Nat :=
  let S := rn.owners
  let top := g.current_step - 1
  g.nodes.foldl (fun (a : Nat × Nat × Nat) p =>
    if !S.contains p.id then a else
    let T := p.owners.filter (fun q => S.contains q)
    let ps := p.parents.filter (fun c => T.contains c)
    let ss := p.sons.filter (fun s => T.contains s)
    let st := p.id.id.step
    let bFail := (st > 0 && ps.isEmpty) || (st < top && ss.isEmpty)
    let ownedBy (c : PathNodeId) (q : PathNodeId) : Bool :=
      match g.node? c with
      | some cn => cn.owners.contains q
      | none => false
    let cFail := T.any (fun q =>
      (st > 0 && !ps.any (fun c => ownedBy c q)) ||
      (st < top && !ss.any (fun s => ownedBy s q)))
    (a.1 + 1, a.2.1 + (if bFail then 1 else 0), a.2.2 + (if cFail then 1 else 0))) (0, 0, 0)

def runSelfSupport (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- is owners(r) self-supporting? cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut choices := 0
  let mut acc : Nat × Nat × Nat := (0, 0, 0)
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let steps := (stepCount φ - 1).toNat
        let mut line := pureInit φ
        for _ in [0:steps] do
          line := pureAdvanceSym φ line
        for kv in line do
          let g := kv.2
          if isValid g then
            for k in intRange 0 (g.current_step - 1) do
              for r in ownersAt g.gowners k do
                match g.node? r with
                | none => pure ()
                | some rn =>
                  choices := choices + 1
                  let t := selfSupport g rn
                  acc := (acc.1 + t.1, acc.2.1 + t.2.1, acc.2.2 + t.2.2)
  IO.println s!"  global owners r examined                  = {choices}"
  IO.println s!"  nodes p in owners(r)                      = {acc.1}"
  IO.println s!"    (b) no parent / son inside T(p)         = {acc.2.1}"
  IO.println s!"    (c) an owner not carried by such a link = {acc.2.2}"
  pure 0


-- ------------------------------------------------------------
-- The greatest fabric inside owners(r)
-- ------------------------------------------------------------

abbrev Tab := List (PathNodeId × List PathNodeId)

def tabOf (T : Tab) (p : PathNodeId) : List PathNodeId :=
  ((T.find? (fun e => e.1 == p)).map (·.2)).getD []

/-- One trimming round of the fabric conditions: drop table entries that are not
symmetric or not carried by a parent and a son inside the table, then drop
members whose table misses a step or no longer holds themselves. -/
def trimFabric (g : GPathM) (T : Tab) : Tab :=
  let top := g.current_step - 1
  let T1 : Tab := T.map (fun e =>
    let p := e.1
    let tp := e.2
    match g.node? p with
    | none => (p, [])
    | some n =>
      (p, tp.filter (fun v =>
        let tv := tabOf T v
        tv.contains p &&
        (p.id.step == 0 || n.parents.any (fun c => tp.contains c && (tabOf T c).contains v)) &&
        (p.id.step == top || n.sons.any (fun s => tp.contains s && (tabOf T s).contains v)))))
  let alive (e : PathNodeId × List PathNodeId) : Bool :=
    e.2.contains e.1 &&
    (intRange 0 (g.current_step - 1)).all (fun k => e.2.any (fun v => v.id.step == k))
  let S2 := (T1.filter alive).map (·.1)
  (T1.filter alive).map (fun e => (e.1, e.2.filter (fun v => S2.contains v)))

partial def gfabric (g : GPathM) (T : Tab) (fuel : Nat) : Tab :=
  let T' := trimFabric g T
  if fuel == 0 || T'.length == T.length &&
      (T'.map (·.2.length)).foldl (· + ·) 0 == (T.map (·.2.length)).foldl (· + ·) 0 then T'
  else gfabric g T' (fuel - 1)

/-- `(members of owners(r), members of the greatest fabric inside it,
entries of owners(p) ∩ owners(r), entries kept)` -/
def fabricInside (g : GPathM) (rn : PNodeM) : Nat × Nat × Nat × Nat :=
  let S0 := g.nodes.filter (fun n => rn.owners.contains n.id)
  let T0 : Tab := S0.map (fun n => (n.id, n.owners.filter (fun v => rn.owners.contains v &&
    (g.nodes.any (fun m => m.id == v)))))
  let Tf := gfabric g T0 1000
  (S0.length, Tf.length, (T0.map (·.2.length)).foldl (· + ·) 0,
   (Tf.map (·.2.length)).foldl (· + ·) 0)

def runFabric (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- the greatest fabric inside owners(r): cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut choices := 0
  let mut full := 0
  let mut acc : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let steps := (stepCount φ - 1).toNat
        let mut line := pureInit φ
        for _ in [0:steps] do
          line := pureAdvanceSym φ line
        for kv in line do
          let g := kv.2
          if isValid g then
            for k in intRange 0 (g.current_step - 1) do
              if PickInduction.choiceAt g k then
                for r in ownersAt g.gowners k do
                  match g.node? r with
                  | none => pure ()
                  | some rn =>
                    choices := choices + 1
                    let t := fabricInside g rn
                    if t.1 == t.2.1 then full := full + 1
                    acc := (acc.1 + t.1, acc.2.1 + t.2.1, acc.2.2.1 + t.2.2.1,
                            acc.2.2.2 + t.2.2.2)
  IO.println s!"  choices r examined                        = {choices}"
  IO.println s!"  nodes in owners(r)                        = {acc.1}"
  IO.println s!"  of those, in the greatest fabric          = {acc.2.1}"
  IO.println s!"  choices where the fabric is ALL owners(r) = {full}"
  IO.println s!"  table entries owners(p) ∩ owners(r)       = {acc.2.2.1}"
  IO.println s!"    kept by the greatest fabric             = {acc.2.2.2}"
  pure 0


-- ------------------------------------------------------------
-- Owners, as the author defines them: exactly the compatible nodes
-- ------------------------------------------------------------

/-- The path a satisfying assignment draws: at step `k`, its map node, with the
previous one as parent. -/
def solPath (φ : Cnf) (a : Assign) (cs : Int) : List PathNodeId :=
  (intRange 0 (cs - 1)).map (fun k =>
    { id := selOfAssign φ a k,
      parent_id := if k == 0 then none else some (selOfAssign φ a (k - 1)) })

/-- Does that path live in `g` as a solution: every node present, a global
owner, linked to its predecessor, and all of them owning each other? -/
def solInside (g : GPathM) (path : List PathNodeId) : Bool :=
  path.all (fun p =>
    g.gowners.contains p &&
    match g.node? p with
    | none => false
    | some n => path.all (fun q => n.owners.contains q)) &&
  (List.range (path.length - 1)).all (fun i =>
    match path[i]?, path[i + 1]? with
    | some a, some b =>
      match g.node? b with
      | some nb => nb.parents.contains a
      | none => false
    | _, _ => false)

structure XAcc where
  states : Nat := 0
  nodes : Nat := 0
  zombieNodes : Nat := 0
  entries : Nat := 0
  spurious : Nat := 0
  notGow : Nat := 0

def addX (a b : XAcc) : XAcc :=
  { states := a.states + b.states, nodes := a.nodes + b.nodes,
    zombieNodes := a.zombieNodes + b.zombieNodes, entries := a.entries + b.entries,
    spurious := a.spurious + b.spurious, notGow := a.notGow + b.notGow }

/-- Exactness of the owner tables against the solutions still inside `g`. -/
def tableExact (φ : Cnf) (sols : List Assign) (g : GPathM) : XAcc := Id.run do
  let inside := (sols.map (fun a => solPath φ a g.current_step)).filter (solInside g)
  let mut acc : XAcc := { states := 1 }
  for n in g.nodes do
    let through := inside.filter (fun path => path.contains n.id)
    acc := { acc with nodes := acc.nodes + 1,
                      zombieNodes := acc.zombieNodes + (if through.isEmpty then 1 else 0),
                      notGow := acc.notGow + (if g.gowners.contains n.id then 0 else 1) }
    for q in n.owners do
      if (g.node? q).isSome then
        acc := { acc with entries := acc.entries + 1,
                          spurious := acc.spurious +
                            (if through.any (fun path => path.contains q) then 0 else 1) }
  return acc

/-- The assignments whose path is on the map up to step `cs - 1`: the solutions
of the clauses the machine has seen so far. -/
def prefixOk (φ : Cnf) (a : Assign) (cs : Int) : Bool :=
  (intRange 0 (cs - 1)).all (fun j => (mapNodes φ j).contains (selOfAssign φ a j))

def runTableExact (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- owners = the compatible nodes? cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut fin : XAcc := {}
  let mut rd : XAcc := {}
  let mut mid : XAcc := {}
  let mut rel : XAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let sols := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat |>.filter (fun a => satB a φ)
        let steps := (stepCount φ - 1).toNat
        let mut line := pureInit φ
        for _ in [0:steps] do
          for kv in line do
            if isValid kv.2 then
              mid := addX mid (tableExact φ sols kv.2)
              let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
              let seen := alls.filter (fun a => prefixOk φ a kv.2.current_step)
              rel := addX rel (tableExact φ seen kv.2)
          line := pureAdvanceSym φ line
        for kv in line do
          if isValid kv.2 then
            fin := addX fin (tableExact φ sols kv.2)
            let mut g := kv.2
            let mut fuel := 200
            let mut go := PickInduction.hasChoice g
            while go do
              fuel := fuel - 1
              match firstChoiceC g with
              | none => go := false
              | some r =>
                g := readStepSym g r
                if isValid g then
                  rd := addX rd (tableExact φ sols g)
                  go := fuel > 0 && PickInduction.hasChoice g
                else go := false
  for (name, x) in [("PARTIAL-length states (control: v60 says inexact)", mid),
                    ("PARTIAL-length states, against the clauses SEEN SO FAR", rel),
                    ("final states of the symmetric machine", fin),
                    ("states along owners-pin reads", rd)] do
    IO.println s!"  --- {name} ---"
    IO.println s!"  states                                    = {x.states}"
    IO.println s!"  nodes / not a global owner                = {x.nodes} / {x.notGow}"
    IO.println s!"  nodes on NO surviving solution            = {x.zombieNodes}"
    IO.println s!"  owner entries (node → node)               = {x.entries}"
    IO.println s!"    on NO common surviving solution         = {x.spurious}"
  pure 0


/-- Diagnostic: list the spurious entries (against the clauses seen so far) of
the partial states of one seed. -/
def runExactDiag (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let steps := (stepCount φ - 1).toNat
        let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
        let sat := alls.any (fun a => satB a φ)
        let mut line := pureInit φ
        let mut stepNo := 0
        for _ in [0:steps] do
          for kv in line do
            let g := kv.2
            if isValid g then
              let seen := alls.filter (fun a => prefixOk φ a g.current_step)
              let inside := (seen.map (fun a => solPath φ a g.current_step)).filter (solInside g)
              for n in g.nodes do
                let through := inside.filter (fun path => path.contains n.id)
                for q in n.owners do
                  if (g.node? q).isSome && !through.any (fun path => path.contains q) then
                    IO.println s!"case {idx} (vars={nVars}, clauses={nClauses}, SAT={sat}) \
cs={g.current_step}/{stepCount φ} key={kv.1.step},{kv.1.index} \
p={n.id.id.step},{n.id.id.index} q={q.id.step},{q.id.index} \
through(p)={through.length} inside={inside.length}"
          line := pureAdvanceSym φ line
          stepNo := stepNo + 1
  pure 0


/-- Targeted hunt: take the formula whose partial state showed a pairwise-but-
not-joint table entry (seed 90210, case 17), append random 3-clauses, and look
for a zombie verdict (valid final state on an UNSAT formula), a final state with
a node on no solution, or a final state whose tables are not exact. -/
def runHunt (trials maxExtra seed : Nat) : IO UInt32 := do
  -- regenerate case 17 of `--tableexact 20 90210 4 3`
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed 90210
  let mut base : Option Cnf := none
  for idx in [0:18] do
    let (rng1, nv) := rng.below 3
    let nVars := 4 + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
    rng := rng3
    if idx == 17 then
      match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
      | .ok φ => base := some φ
      | .error _ => pure ()
  match base with
  | none => IO.println "base formula not found"; pure 1
  | some φ0 =>
  IO.println s!"--- hunt from seed 90210 case 17: nVars={φ0.nVars} clauses={φ0.clauses.length} \
trials={trials} extra≤{maxExtra} ---"
  let mut r := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut tested := 0
  let mut unsat := 0
  let mut zombieVerdict := 0
  let mut zombieNode := 0
  let mut inexact := 0
  let mut entries := 0
  for _ in [0:trials] do
    let (r1, j) := r.below maxExtra
    r := r1
    let mut extra : List Clause := []
    for _ in [0:j + 1] do
      let n := φ0.nVars
      let (r2, a) := r.below n
      let (r3, b0) := r2.below (n - 1)
      let (r4, c0) := r3.below (n - 2)
      let b := if b0 >= a then b0 + 1 else b0
      let lo := min a b
      let hi := max a b
      let c1 := if c0 >= lo then c0 + 1 else c0
      let c := if c1 >= hi then c1 + 1 else c1
      let (r5, s) := r4.below 8
      r := r5
      extra := extra ++ [{ l1 := { v := a, pos := s % 2 == 0 },
                           l2 := { v := b, pos := (s / 2) % 2 == 0 },
                           l3 := { v := c, pos := (s / 4) % 2 == 0 } }]
    let φ : Cnf := { φ0 with clauses := φ0.clauses ++ extra }
    if AbsSat.Cnf.Dimacs.wfB φ then
      tested := tested + 1
      let sols := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat |>.filter (fun a => satB a φ)
      if sols.isEmpty then unsat := unsat + 1
      let steps := (stepCount φ - 1).toNat
      let mut line := pureInit φ
      for _ in [0:steps] do
        line := pureAdvanceSym φ line
      let finals := line.filter (fun kv => isValid kv.2)
      if sols.isEmpty && !finals.isEmpty then
        zombieVerdict := zombieVerdict + 1
        IO.println s!"  ZOMBIE VERDICT: extra={repr extra}"
      for kv in finals do
        let x := tableExact φ sols kv.2
        zombieNode := zombieNode + x.zombieNodes
        inexact := inexact + x.spurious
        entries := entries + x.entries
  IO.println s!"  formulas tested                           = {tested} ({unsat} UNSAT)"
  IO.println s!"  ZOMBIE VERDICTS (valid on UNSAT)          = {zombieVerdict}"
  IO.println s!"  final-state nodes on no solution          = {zombieNode}"
  IO.println s!"  final-state owner entries / inexact       = {entries} / {inexact}"
  pure 0


-- ------------------------------------------------------------
-- Tseitin formulas on 3-regular graphs
-- ------------------------------------------------------------

/-- Parity constraint `e₁ ⊕ e₂ ⊕ e₃ = c` as the four 3-clauses that forbid
the wrong-parity rows. Variables are edge indices. -/
def xorClauses (e1 e2 e3 : Nat) (c : Bool) : List Clause :=
  (List.range 8).filterMap (fun m =>
    let b1 := m % 2 == 1
    let b2 := (m / 2) % 2 == 1
    let b3 := (m / 4) % 2 == 1
    let parity := (b1 != b2) != b3
    if parity == c then none
    else some { l1 := { v := e1, pos := !b1 }, l2 := { v := e2, pos := !b2 },
                l3 := { v := e3, pos := !b3 } })

/-- Tseitin formula of a 3-regular graph given by its edge list; `odd` puts
charge 1 on vertex 0 (total parity odd ⇒ UNSAT), otherwise all charges 0 (SAT). -/
def tseitin (nV : Nat) (edges : List (Nat × Nat)) (odd : Bool) : Option Cnf := do
  let mut cls : List Clause := []
  for v in List.range nV do
    let inc := (List.range edges.length).filter (fun i =>
      match edges[i]? with
      | some (a, b) => a == v || b == v
      | none => false)
    match inc with
    | [e1, e2, e3] => cls := cls ++ xorClauses e1 e2 e3 (odd && v == 0)
    | _ => none
  return { nVars := edges.length, clauses := cls }

def k4 : List (Nat × Nat) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def k33 : List (Nat × Nat) := [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]
def prism : List (Nat × Nat) := [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]
def cube : List (Nat × Nat) :=
  [(0,1),(1,3),(3,2),(2,0),(4,5),(5,7),(7,6),(6,4),(0,4),(1,5),(2,6),(3,7)]
def petersen : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

/-- Relabel edges (variables) by a permutation drawn from `rng`, and shuffle
the clause order: the machine's map depends on both. -/
def shuffleList {α : Type} (rng : AbsSat.SatMachine.DiffTest.Rng) (l : List α) :
    AbsSat.SatMachine.DiffTest.Rng × List α := Id.run do
  let mut r := rng
  let mut src := l
  let mut out : List α := []
  while !src.isEmpty do
    let (r1, i) := r.below src.length
    r := r1
    match src[i]? with
    | some x =>
      out := out ++ [x]
      src := src.eraseIdx i
    | none => src := []
  return (r, out)

def machineSat (φ : Cnf) (sym : Bool) : Bool := Id.run do
  let steps := (stepCount φ - 1).toNat
  let mut line := pureInit φ
  for _ in [0:steps] do
    line := if sym then pureAdvanceSym φ line else pureAdvance φ line
  return line.any (fun kv => isValid kv.2)

def runTseitin (perms seed maxGraphs : Nat) : IO UInt32 := do
  IO.println s!"--- Tseitin formulas on 3-regular graphs: {perms} orderings each, seed={seed} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut zombies := 0
  let graphs := [("K4", 4, k4), ("K3,3", 6, k33), ("prism", 6, prism),
                 ("cube", 8, cube), ("Petersen", 10, petersen)]
  for (name, nV, edges) in graphs.take maxGraphs do
    let mut oddSat := 0
    let mut oddSatSym := 0
    let mut evenSat := 0
    let mut tested := 0
    for _ in [0:perms] do
      let (r1, perm) := shuffleList rng (List.range edges.length)
      rng := r1
      let edges' := (List.range edges.length).filterMap (fun i => edges[perm[i]!]?)
      for odd in [true, false] do
        match tseitin nV edges' odd with
        | none => pure ()
        | some φ0 =>
          let (r2, cls) := shuffleList rng φ0.clauses
          rng := r2
          let φ : Cnf := { φ0 with clauses := cls }
          if AbsSat.Cnf.Dimacs.wfB φ then
            if odd then
              tested := tested + 1
              if machineSat φ false then oddSat := oddSat + 1
              if machineSat φ true then oddSatSym := oddSatSym + 1
            else
              if machineSat φ false then evenSat := evenSat + 1
    zombies := zombies + oddSat + oddSatSym
    IO.println s!"  {name}: vars={edges.length} clauses={4 * nV}  UNSAT versions={tested}  \
machine says SAT (ZOMBIE): original={oddSat} symmetric={oddSatSym}  \
SAT versions answered SAT={evenSat}/{perms}"
    (← IO.getStdout).flush
  IO.println s!"--- zombie verdicts: {zombies} ---"
  pure 0


/-- Nodes of `g` on no solution (of the clauses seen so far) living inside it. -/
def nodeZombies (φ : Cnf) (alls : List Assign) (g : GPathM) : Nat :=
  let seen := alls.filter (fun a => prefixOk φ a g.current_step)
  let inside := (seen.map (fun a => solPath φ a g.current_step)).filter (solInside g)
  (g.nodes.filter (fun n => !inside.any (fun path => path.contains n.id))).length

/-- **Aimed at the clause filter.** Take the formula whose partial state held
pairwise-compatible-but-not-joint entries (seed 90210, case 17), insert one
3-clause at each position in `[lo, hi)`, over every triple of variables and
every sign pattern, and run the ORIGINAL machine: count states with a node on
no solution of the clauses seen so far — a direct violation of
`ClauseStepExact` — and zombie verdicts. -/
def runInsert (lo hi : Nat) : IO UInt32 := do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed 90210
  let mut base : Option Cnf := none
  for idx in [0:18] do
    let (rng1, nv) := rng.below 3
    let nVars := 4 + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
    rng := rng3
    if idx == 17 then
      match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
      | .ok φ => base := some φ
      | .error _ => pure ()
  match base with
  | none => IO.println "base not found"; pure 1
  | some φ0 =>
  let n := φ0.nVars
  let alls := (List.range (Nat.pow 2 n)).map assignOfNat
  IO.println s!"--- clause insertion at positions [{lo},{hi}) of seed 90210 case 17 \
(nVars={n}, clauses={φ0.clauses.length}) ---"
  let mut runs := 0
  let mut badStates := 0
  let mut badNodes := 0
  let mut zverdict := 0
  for j in [lo:hi] do
    for a in [0:n] do
      for b in [a+1:n] do
        for c in [b+1:n] do
          for s in [0:8] do
            let C : Clause := { l1 := { v := a, pos := s % 2 == 0 },
                                l2 := { v := b, pos := (s / 2) % 2 == 0 },
                                l3 := { v := c, pos := (s / 4) % 2 == 0 } }
            let φ : Cnf := { φ0 with clauses := φ0.clauses.take j ++ [C] ++ φ0.clauses.drop j }
            if AbsSat.Cnf.Dimacs.wfB φ then
              runs := runs + 1
              let truth := alls.any (fun x => satB x φ)
              let steps := (stepCount φ - 1).toNat
              let mut line := pureInit φ
              let mut bad := false
              for _ in [0:steps] do
                line := pureAdvance φ line
                for kv in line do
                  if isValid kv.2 then
                    let z := nodeZombies φ alls kv.2
                    if z > 0 then
                      badStates := badStates + 1
                      badNodes := badNodes + z
                      if !bad then
                        IO.println s!"  VIOLATION: insert at {j} clause {repr C} → state \
cs={kv.2.current_step} key={kv.1.step},{kv.1.index}: {z} node(s) on no solution"
                        (← IO.getStdout).flush
                      bad := true
              let v := line.any (fun kv => isValid kv.2)
              if v && !truth then
                zverdict := zverdict + 1
                IO.println s!"  ZOMBIE VERDICT: insert at {j} clause {repr C}"
                (← IO.getStdout).flush
  IO.println s!"  formulas run                              = {runs}"
  IO.println s!"  states with a node on no solution         = {badStates} ({badNodes} nodes)"
  IO.println s!"  zombie verdicts                           = {zverdict}"
  pure 0


-- ------------------------------------------------------------
-- How often each case of the clause filter's decomposition fires
-- ------------------------------------------------------------

structure FAcc where
  filters : Nat := 0
  instances : Nat := 0
  caseA : Nat := 0
  caseC : Nat := 0
  caseBonly : Nat := 0
  caseD : Nat := 0
  caseDfail : Nat := 0

/-- For every clause-step filter of the ORIGINAL machine, every surviving node
`p` and every requirement `r` (in order, `S` = the ones before it), classify the
step of `ClauseFilter.OneReqStep_of_FlipCore`:
(a) `p` at `r`'s step; (c) `r`'s step already pinned; otherwise look at the
solutions of `g` through `p` carrying `S`: if all carry `r`, case (b) always
applies; if some carry the other value, the core (d) can be invoked — resolved
when some solution carries `r`, FAILED when none does. -/
def runFlipCases (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- the cases of the clause filter: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : FAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
        let steps := (stepCount φ - 1).toNat
        let mut line := pureInit φ
        for _ in [0:steps] do
          for kv in line do
            let g := kv.2
            if isValid g then
              for d in mapSons φ kv.1.step kv.1.index do
                if litBlock φ < d.step && d.step < fusionTop φ then
                  let reqs := reqOfCnf φ d
                  let h := filterAll g reqs
                  if isValid h then
                    acc := { acc with filters := acc.filters + 1 }
                    let seen := alls.filter (fun a => prefixOk φ a g.current_step)
                    let inside := (seen.map (fun a => solPath φ a g.current_step)).filter (solInside g)
                    for n in h.nodes do
                      let p := n.id
                      for i in [0:reqs.length] do
                        match reqs[i]? with
                        | none => pure ()
                        | some r =>
                          let S := reqs.take i
                          acc := { acc with instances := acc.instances + 1 }
                          let carries (path : List PathNodeId) (x : NodeId) : Bool :=
                            match path[x.step.toNat]? with
                            | some y => y.id == x
                            | none => false
                          if p.id.step == r.step then
                            acc := { acc with caseA := acc.caseA + 1 }
                          else if g.gowners.all (fun q => q.id.step != r.step || q.id == r) then
                            acc := { acc with caseC := acc.caseC + 1 }
                          else
                            let through := inside.filter (fun path =>
                              path.contains p && S.all (fun x => carries path x))
                            if through.all (fun path => carries path r) then
                              acc := { acc with caseBonly := acc.caseBonly + 1 }
                            else if through.any (fun path => carries path r) then
                              acc := { acc with caseD := acc.caseD + 1 }
                            else
                              acc := { acc with caseDfail := acc.caseDfail + 1 }
          line := pureAdvance φ line
  IO.println s!"  clause-step filters (valid)               = {acc.filters}"
  IO.println s!"  (survivor, requirement) instances         = {acc.instances}"
  IO.println s!"    (a) survivor at the requirement's step  = {acc.caseA}"
  IO.println s!"    (c) step already pinned                 = {acc.caseC}"
  IO.println s!"    (b) every chain already carries it      = {acc.caseBonly}"
  IO.println s!"    (d) core needed, and a flip exists      = {acc.caseD}"
  IO.println s!"    (d) core needed, NO flip exists (FAIL)  = {acc.caseDfail}"
  pure 0


/-- Dump of seed 90210 case 17 at the state where the 18 entries appear. -/
def runCase17 : IO UInt32 := do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed 90210
  let mut base : Option Cnf := none
  for idx in [0:18] do
    let (rng1, nv) := rng.below 3
    let nVars := 4 + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
    rng := rng3
    if idx == 17 then
      match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
      | .ok φ => base := some φ
      | .error _ => pure ()
  match base with
  | none => pure 1
  | some φ =>
  let lit (l : Lit) : String := (if l.pos then "x" else "¬x") ++ toString l.v
  IO.println s!"nVars={φ.nVars} clauses={φ.clauses.length} litBlock={litBlock φ}"
  for i in [0:5] do
    match φ.clauses[i]? with
    | some c => IO.println s!"  clause {i} (step {litBlock φ + 1 + i}): {lit c.l1} ∨ {lit c.l2} ∨ {lit c.l3}"
    | none => pure ()
  let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
  for sym in [true, false] do
    IO.println s!"=== {if sym then "symmetric" else "original"} machine ==="
    let mut line := pureInit φ
    for _ in [0:17] do
      line := if sym then pureAdvanceSym φ line else pureAdvance φ line
    for kv in line do
      let g := kv.2
      if isValid g && kv.1.step == 17 && kv.1.index == 4 then
        let seen := alls.filter (fun a => prefixOk φ a g.current_step)
        let inside := seen.filter (fun a => solInside g (solPath φ a g.current_step))
        IO.println s!"state key=(17,4) cs={g.current_step} nodes={g.nodes.length}"
        IO.println s!"  seen-so-far solutions: {seen.length}; inside this state: {inside.length}"
        for a in inside do
          IO.println s!"    x0..x5 = {(List.range φ.nVars).map (fun v => if a v then 1 else 0)}"
        let t := triangle g
        IO.println s!"  triangle: pairs={t.1} gaps={t.2}"
        -- spurious entries and their witnesses
        let paths := inside.map (fun a => solPath φ a g.current_step)
        for n in g.nodes do
          for q in n.owners do
            if n.id.id.step < q.id.step && (g.node? q).isSome &&
               !paths.any (fun pa => pa.contains n.id && pa.contains q) then
              let pp := match n.id.parent_id with | some x => s!"{x.step},{x.index}" | none => "-"
              let qp := match q.parent_id with | some x => s!"{x.step},{x.index}" | none => "-"
              -- which steps have no common owner of p and q?
              let gapSteps := (intRange 0 (g.current_step - 1)).filter (fun k =>
                match g.node? q with
                | some qn => !(n.owners.any (fun w => w.id.step == k && qn.owners.contains w))
                | none => true)
              IO.println s!"  spurious: p=({n.id.id.step},{n.id.id.index}|{pp}) \
q=({q.id.step},{q.id.index}|{qp})  steps with no common owner: {gapSteps}"
  pure 0


-- ------------------------------------------------------------
-- The machine with the triangle pass
-- ------------------------------------------------------------

def sendToTri (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  let g' := TriReview.upFilteringTri g (reqOfCnf φ d) d ""
  if isValid g' then insertPure next d g' else next

def pureAdvanceTri (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv =>
    (mapSons φ kv.1.step kv.1.index).foldl (sendToTri φ kv.2) next) []

/-- Original machine against the machine with the triangle pass: verdicts, and
exactness of the tables against the clauses seen so far, at every state. -/
def runTri (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- triangle pass: cases={cases} seed={seed} vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut sat := 0
  let mut agree := 0
  let mut lost := 0
  let mut zomb := 0
  let mut o : XAcc := {}
  let mut t : XAcc := {}
  let mut oGaps := 0
  let mut tGaps := 0
  let mut inst := 0
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        inst := inst + 1
        let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
        let truth := alls.any (fun a => satB a φ)
        if truth then sat := sat + 1
        let steps := (stepCount φ - 1).toNat
        let mut lo := pureInit φ
        let mut lt := pureInit φ
        for _ in [0:steps] do
          lo := pureAdvance φ lo
          lt := pureAdvanceTri φ lt
          for kv in lo do
            if isValid kv.2 then
              let seen := alls.filter (fun a => prefixOk φ a kv.2.current_step)
              o := addX o (tableExact φ seen kv.2)
              oGaps := oGaps + (triangle kv.2).2
          for kv in lt do
            if isValid kv.2 then
              let seen := alls.filter (fun a => prefixOk φ a kv.2.current_step)
              t := addX t (tableExact φ seen kv.2)
              tGaps := tGaps + (triangle kv.2).2
        let vo := lo.any (fun kv => isValid kv.2)
        let vt := lt.any (fun kv => isValid kv.2)
        if vo == vt then agree := agree + 1
        if truth && !vt then lost := lost + 1
        if !truth && vt then zomb := zomb + 1
  IO.println s!"  formulas / satisfiable                    = {inst} / {sat}"
  IO.println s!"  verdicts equal to the original's          = {agree}"
  IO.println s!"  LOST A SOLUTION / ZOMBIE VERDICT (tri)    = {lost} / {zomb}"
  IO.println s!"  --- every state after the first, against the clauses seen so far ---"
  IO.println s!"  original: states={o.states} nodes={o.nodes} zombieNodes={o.zombieNodes} \
entries={o.entries} spurious={o.spurious} triangleGaps={oGaps}"
  IO.println s!"  triangle: states={t.states} nodes={t.nodes} zombieNodes={t.zombieNodes} \
entries={t.entries} spurious={t.spurious} triangleGaps={tGaps}"
  pure 0


/-- Triple exactness in the triangle machine's states: sample triples of nodes
that pairwise own each other and ask whether one solution (of the clauses seen
so far, living in the state) passes all three. -/
def runTriples (cases seed nvMin nvSpan samples : Nat) : IO UInt32 := do
  IO.println s!"--- triples in the triangle machine: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} samples/state={samples} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut states := 0
  let mut tested := 0
  let mut gaps := 0
  let mut pairGaps := 0
  let mut mapGaps := 0
  let mut shown := 0
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
        let steps := (stepCount φ - 1).toNat
        let mut lt := pureInit φ
        let mut r := AbsSat.SatMachine.DiffTest.Rng.ofSeed (seed * 7919 + idx)
        for _ in [0:steps] do
          lt := pureAdvanceTri φ lt
          for kv in lt do
            let g := kv.2
            if isValid g then
              states := states + 1
              let seen := alls.filter (fun a => prefixOk φ a g.current_step)
              let inside := (seen.map (fun a => solPath φ a g.current_step)).filter (solInside g)
              let ns := g.nodes.toArray
              if ns.size ≥ 3 then
                for _ in [0:samples] do
                  let (r1, i) := r.below ns.size
                  let (r2, j) := r1.below ns.size
                  let (r3, k) := r2.below ns.size
                  r := r3
                  match ns[i]?, ns[j]?, ns[k]? with
                  | some a, some b, some c =>
                    let steps3 := [a.id.id.step, b.id.id.step, c.id.id.step]
                    if steps3.eraseDups.length == 3 &&
                       a.owners.contains b.id && a.owners.contains c.id &&
                       b.owners.contains a.id && b.owners.contains c.id &&
                       c.owners.contains a.id && c.owners.contains b.id then
                      tested := tested + 1
                      let both (x y : PathNodeId) := inside.any (fun p => p.contains x && p.contains y)
                      if !(both a.id b.id && both a.id c.id && both b.id c.id) then
                        pairGaps := pairGaps + 1
                      else if !inside.any (fun p => p.contains a.id && p.contains b.id && p.contains c.id) then
                        gaps := gaps + 1
                        -- is the gap already there between the map values (ignoring parents)?
                        let hasId (p : List PathNodeId) (x : PathNodeId) : Bool :=
                          p.any (fun y => y.id == x.id)
                        if !inside.any (fun p => hasId p a.id && hasId p b.id && hasId p c.id) then
                          mapGaps := mapGaps + 1
                          let seenPaths := seen.map (fun a => solPath φ a g.current_step)
                          let global := seenPaths.any (fun p => hasId p a.id && hasId p b.id && hasId p c.id)
                          IO.println s!"  MAP GAP (combination {if global then "EXISTS elsewhere" else "ABSENT everywhere"}): case={idx} nVars={φ.nVars} clauses={φ.clauses.length} \
cs={g.current_step} key=({kv.1.step},{kv.1.index}) \
({a.id.id.step},{a.id.id.index}) ({b.id.id.step},{b.id.id.index}) ({c.id.id.step},{c.id.id.index})"
                        if shown < 5 then
                          shown := shown + 1
                          IO.println s!"  TRIPLE GAP: case={idx} nVars={φ.nVars} clauses={φ.clauses.length} cs={g.current_step} \
({a.id.id.step},{a.id.id.index}) ({b.id.id.step},{b.id.id.index}) ({c.id.id.step},{c.id.id.index})"
                  | _, _, _ => pure ()
  IO.println s!"  states                                    = {states}"
  IO.println s!"  co-owned triples tested                   = {tested}"
  IO.println s!"    with a pair on no common solution       = {pairGaps}"
  IO.println s!"    pairwise fine, NO common solution (gap) = {gaps}"
  IO.println s!"      of which also a gap between map values = {mapGaps}"
  pure 0


/-- The `idx`-th formula of the standard campaign generator. -/
def genCase (seed nvMin nvSpan idx : Nat) : Option Cnf := Id.run do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut out : Option Cnf := none
  for i in [0:idx + 1] do
    let (rng1, nv) := rng.below nvSpan
    let nVars := nvMin + nv
    let (rng2, nClauses) :=
      if i % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
    rng := rng3
    if i == idx then
      match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
      | .ok φ => out := some φ
      | .error _ => pure ()
  return out

/-- Insert one 3-clause (every triple, every sign pattern) at each position in
`[lo, hi)` of a chosen formula, run the chosen machine, and count states with a
node on no solution of the clauses seen so far, and zombie verdicts. -/
def runInsertGen (seed nvMin nvSpan idx lo hi : Nat) (tri : Bool) : IO UInt32 := do
  match genCase seed nvMin nvSpan idx with
  | none => IO.println "no formula"; pure 1
  | some φ0 =>
  let n := φ0.nVars
  let alls := (List.range (Nat.pow 2 n)).map assignOfNat
  IO.println s!"--- insertion into seed {seed} case {idx} (nVars={n}, clauses={φ0.clauses.length}) \
positions [{lo},{hi}), machine={if tri then "triangle" else "original"} ---"
  (← IO.getStdout).flush
  let mut runs := 0
  let mut badStates := 0
  let mut zverdict := 0
  let mut shown := 0
  for j in [lo:hi] do
    for a in [0:n] do
      for b in [a+1:n] do
        for c in [b+1:n] do
          for s in [0:8] do
            let C : Clause := { l1 := { v := a, pos := s % 2 == 0 },
                                l2 := { v := b, pos := (s / 2) % 2 == 0 },
                                l3 := { v := c, pos := (s / 4) % 2 == 0 } }
            let φ : Cnf := { φ0 with clauses := φ0.clauses.take j ++ [C] ++ φ0.clauses.drop j }
            if AbsSat.Cnf.Dimacs.wfB φ then
              runs := runs + 1
              let truth := alls.any (fun x => satB x φ)
              let steps := (stepCount φ - 1).toNat
              let mut line := pureInit φ
              for _ in [0:steps] do
                line := if tri then pureAdvanceTri φ line else pureAdvance φ line
                for kv in line do
                  if isValid kv.2 then
                    let z := nodeZombies φ alls kv.2
                    if z > 0 then
                      badStates := badStates + 1
                      if shown < 8 then
                        shown := shown + 1
                        IO.println s!"  NODE ZOMBIE: insert at {j} clause {repr C} → \
cs={kv.2.current_step} key=({kv.1.step},{kv.1.index}): {z} node(s) on no solution"
                        (← IO.getStdout).flush
              if !truth && line.any (fun kv => isValid kv.2) then
                zverdict := zverdict + 1
                IO.println s!"  ZOMBIE VERDICT: insert at {j} clause {repr C}"
                (← IO.getStdout).flush
  IO.println s!"  formulas run                              = {runs}"
  IO.println s!"  states with a node on no solution         = {badStates}"
  IO.println s!"  zombie verdicts                           = {zverdict}"
  pure 0


-- ------------------------------------------------------------
-- The bounded-scope class: does the constructive repair work?
-- ------------------------------------------------------------

/-! What `FlipCore` needs, stripped of the machine, is a **repair**: given a
solution of the clauses seen so far that respects some pins, and one more
literal to satisfy, produce another solution respecting the pins *and* the new
literal. The proof planned for the bounded-scope class does it constructively —
flip the target, then walk the broken clauses in GYO ear order, fixing one
variable at a time — so what has to be measured before writing any Lean is not
whether a repaired solution *exists* (v68 already measured that: 0 failures)
but whether **this construction finds it**, and whether the class is what
separates the cases where it does from the cases where it does not.

The control is built in: the same procedure runs on the Tseitin formulas, which
are outside the class, and it must fail there. A procedure that succeeds
everywhere would be measuring nothing. -/

def setVar (a : Assign) (v : Nat) (b : Bool) : Assign := fun u => if u == v then b else a u

def satClauseB (a : Assign) (c : Clause) : Bool :=
  litVal a c.l1 || litVal a c.l2 || litVal a c.l3

/-- The first clause the assignment breaks. -/
def brokenClause (C : List Clause) (a : Assign) : Option Clause :=
  C.find? (fun c => !(satClauseB a c))

/-- How many clauses a variable occurs in. The GYO ear order prefers the
least-occurring variable: occurring once *is* being an ear. -/
def varOccurs (C : List Clause) (v : Nat) : Nat :=
  (C.filter (fun c => c.l1.v == v || c.l2.v == v || c.l3.v == v)).length

/-- **The constructive repair.** Each step takes a broken clause and sets one
of its unlocked variables to satisfy it, locking that variable. `ear` picks the
least-occurring variable (the GYO order), otherwise the leftmost. A step that
finds every variable of a broken clause already locked FAILS — that is exactly
the case the bounded-scope hypothesis has to rule out. Terminates because every
step locks one more variable. -/
def repairGo (C : List Clause) (ear : Bool) : Nat → List Nat → Assign → Option Assign
  | 0, _, _ => none
  | fuel + 1, locked, a =>
    match brokenClause C a with
    | none => some a
    | some c =>
      let cands := [c.l1, c.l2, c.l3].filter (fun l => !locked.contains l.v)
      let pick :=
        if ear then
          cands.foldl (fun best l =>
            match best with
            | none => some l
            | some w => if varOccurs C l.v < varOccurs C w.v then some l else some w) none
        else cands.head?
      match pick with
      | none => none
      | some l => repairGo C ear fuel (l.v :: locked) (setVar a l.v l.pos)

/-- Flip `v` to `b` and repair, keeping `pins` (and `v`) fixed throughout. -/
def repairFlip (C : List Clause) (nVars : Nat) (ear : Bool) (a : Assign) (pins : List Nat)
    (v : Nat) (b : Bool) : Option Assign :=
  repairGo C ear (nVars + 1) (v :: pins) (setVar a v b)

/-! ### The repair by **rows**

The variable-at-a-time repair above gets stuck, and the stuck cases say why:
they are formulas whose clauses all range over the *same* variables. As a
hypergraph that is a single edge — trivially α-acyclic — but as a constraint it
is the intersection of several relations over that scope, and no amount of
acyclicity helps a procedure that fixes one variable at a time and never
reconsiders.

The machine does not work that way, and neither does the classical algorithm
for acyclic CSPs. A clause node of the map encodes its **three literals at
once**: the unit the machine moves is a *row*, not a variable. So the repair
has to move rows too — pick, for a violated scope, a whole row of the relation
that scope carries. -/

/-- A scope: the distinct variables a clause ranges over, sorted. -/
def clauseScope (c : Clause) : List Nat :=
  ([c.l1.v, c.l2.v, c.l3.v].foldl (fun acc v =>
    if acc.contains v then acc else acc ++ [v]) []).mergeSort (fun x y => x ≤ y)

/-- The distinct scopes of `C`. Two clauses over the same variables are one
relation, not two — which is exactly what the hypergraph already says, since
`dropSubsumed` dedups identical edges. -/
def scopesOf (C : List Clause) : List (List Nat) :=
  C.foldl (fun acc c =>
    let s := clauseScope c
    if acc.contains s then acc else acc ++ [s]) []

/-- The rows a scope allows: assignments to its variables satisfying **every**
clause of `C` with that scope. Represented as the list of values, aligned with
the scope's variable list. -/
def rowsOf (C : List Clause) (s : List Nat) : List (List Bool) :=
  let cls := C.filter (fun c => clauseScope c == s)
  (List.range (Nat.pow 2 s.length)).filterMap (fun m =>
    let vals := (List.range s.length).map (fun i => m.testBit i)
    let a : Assign := fun u =>
      match s.idxOf? u with
      | some i => vals[i]!
      | none => false
    if cls.all (satClauseB a) then some vals else none)

def applyRow (a : Assign) (s : List Nat) (vals : List Bool) : Assign := fun u =>
  match s.idxOf? u with
  | some i => vals[i]!
  | none => a u

/-- A scope some clause of which the assignment breaks. -/
def brokenScope (C : List Clause) (a : Assign) : Option (List Nat) :=
  (C.find? (fun c => !(satClauseB a c))).map clauseScope

/-- **The repair, by rows.** Each step takes a violated scope and installs a
whole row of its relation that agrees with everything locked so far, locking
the scope's variables. Stuck when the violated scope has no such row — the case
the class has to rule out. Terminates: a violated scope always contains an
unlocked variable (if all were locked, its values would already be a locked
row), so every step locks one more. -/
def repairRowGo (C : List Clause) : Nat → List Nat → Assign → Option Assign
  | 0, _, _ => none
  | fuel + 1, locked, a =>
    match brokenScope C a with
    | none => some a
    | some s =>
      let ok := (rowsOf C s).filter (fun vals =>
        (List.range s.length).all (fun i =>
          match s[i]? with
          | some u => !locked.contains u || vals[i]! == a u
          | none => true))
      match ok.head? with
      | none => none
      | some vals => repairRowGo C fuel (locked ++ s) (applyRow a s vals)

def repairFlipRow (C : List Clause) (nVars : Nat) (a : Assign) (pins : List Nat)
    (v : Nat) (b : Bool) : Option Assign :=
  repairRowGo C (nVars + 1) (v :: pins) (setVar a v b)

/-! ### The repair by rows, **after the reducer**

The row repair still gets stuck, and again the stuck cases say why. Two scopes
sharing two variables: the greedy picks a row of the first that is locally fine
and globally dead — no row of the second agrees with it — and there is no way
back. What removes such rows is the **semi-join**: drop from each relation
every row unsupported by a neighbour, to the fixpoint. That is arc consistency
on the relations, and it is exactly what the machine's `review` passes do to
the owners tables (`ArcConsistency.review_arcConsistent`). The classical
theorem is that on an α-acyclic hypergraph the reduced relations can then be
picked greedily with no backtracking — so this, and not the bare greedy, is the
procedure the bounded-scope proof has to mirror. -/

structure Rel where
  scope : List Nat
  rows : List (List Bool)

def rowVal (s : List Nat) (vals : List Bool) (u : Nat) : Option Bool :=
  match s.idxOf? u with
  | some i => vals[i]?
  | none => none

/-- Two rows agree wherever their scopes overlap. -/
def rowsAgree (s : List Nat) (vals : List Bool) (t : List Nat) (w : List Bool) : Bool :=
  s.all (fun u =>
    match rowVal s vals u, rowVal t w u with
    | some x, some y => x == y
    | _, _ => true)

/-- One semi-join sweep: a row survives only if every other relation has a row
agreeing with it. -/
def reduceOnce (rels : List Rel) : List Rel :=
  rels.map (fun r =>
    { r with rows := r.rows.filter (fun vals =>
        rels.all (fun q => q.scope == r.scope ||
          q.rows.any (fun w => rowsAgree r.scope vals q.scope w))) })

def reduceGo : Nat → List Rel → List Rel
  | 0, rels => rels
  | n + 1, rels =>
    let rels' := reduceOnce rels
    if rels'.map (·.rows) == rels.map (·.rows) then rels else reduceGo n rels'

/-- Narrow every relation by the variables already fixed. -/
def pinRels (locked : List (Nat × Bool)) (rels : List Rel) : List Rel :=
  rels.map (fun r =>
    { r with rows := r.rows.filter (fun vals =>
        locked.all (fun p =>
          match rowVal r.scope vals p.1 with
          | some x => x == p.2
          | none => true)) })

/-- **The repair the proof would mirror.** Pin the target and the pins, reduce
to the arc-consistent fixpoint, then take relations one at a time: install the
first surviving row, re-pin, re-reduce. Stuck when some relation empties. -/
def repairReduceGo : Nat → Nat → List Rel → List (Nat × Bool) → List Rel →
    Option (List (Nat × Bool))
  | 0, _, _, locked, _ => some locked
  | n + 1, fuel, rels, locked, all =>
    match rels with
    | [] => some locked
    | r :: rest =>
      match r.rows.head? with
      | none => none
      | some vals =>
        let locked' := locked ++ (List.range r.scope.length).filterMap (fun i =>
          match r.scope[i]?, vals[i]? with
          | some u, some x => some (u, x)
          | _, _ => none)
        let all' := reduceGo fuel (pinRels locked' all)
        if all'.any (fun q => q.rows.isEmpty) then none
        else
          let rest' := rest.filterMap (fun q => all'.find? (fun w => w.scope == q.scope))
          repairReduceGo n fuel rest' locked' all'

def repairFlipReduce (C : List Clause) (a : Assign) (pins : List Nat)
    (v : Nat) (b : Bool) : Option Assign :=
  let rels := (scopesOf C).map (fun s => { scope := s, rows := rowsOf C s : Rel })
  let locked := (v, b) :: pins.map (fun u => (u, a u))
  let fuel := rels.length + 2
  let rels0 := reduceGo fuel (pinRels locked rels)
  if rels0.any (fun q => q.rows.isEmpty) then none
  else
    match repairReduceGo (rels0.length + 1) fuel rels0 locked rels0 with
    | none => none
    | some final => some (fun u =>
        match final.find? (fun p => p.1 == u) with
        | some p => p.2
        | none => a u)

structure RAcc where
  formulas : Nat := 0
  instances : Nat := 0
  repaired : Nat := 0
  failedStuck : Nat := 0
  failedWrong : Nat := 0

def RAcc.add (x : RAcc) (y : RAcc) : RAcc :=
  { formulas := x.formulas + y.formulas, instances := x.instances + y.instances,
    repaired := x.repaired + y.repaired, failedStuck := x.failedStuck + y.failedStuck,
    failedWrong := x.failedWrong + y.failedWrong }

/-- The three repair strategies measured: by variable in GYO ear order, by
variable leftmost-first, and by row. -/
inductive RepairMode where
  | ear | first | row | reduce

def runRepair (mode : RepairMode) (C : List Clause) (nVars : Nat) (a : Assign)
    (pins : List Nat) (v : Nat) (b : Bool) : Option Assign :=
  match mode with
  | .ear => repairFlip C nVars true a pins v b
  | .first => repairFlip C nVars false a pins v b
  | .row => repairFlipRow C nVars a pins v b
  | .reduce => repairFlipReduce C a pins v b

/-- Run the repair on every prefix of one formula, over sampled (solution,
pins, target) triples for which a repaired solution is known to exist. The
three modes see the *same* triples: the rng is threaded once and replayed. -/
def scoreFormula (φ : Cnf) (mode : RepairMode) (solCap pinTries : Nat)
    (rng0 : AbsSat.SatMachine.DiffTest.Rng) :
    AbsSat.SatMachine.DiffTest.Rng × RAcc := Id.run do
  let mut rng := rng0
  let mut acc : RAcc := { formulas := 1 }
  let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
  for m in [0:φ.clauses.length + 1] do
    let C := φ.clauses.take m
    let sols := alls.filter (fun a => C.all (satClauseB a))
    for a in sols.take solCap do
      for v in [0:φ.nVars] do
        let b := !(a v)
        for _ in [0:pinTries] do
          let (r1, mask) := rng.below (Nat.pow 2 φ.nVars)
          rng := r1
          let pins := ((List.range φ.nVars).filter
            (fun u => u != v && mask.testBit u)).take 5
          -- only ask the question where a repaired solution exists at all
          let exists_ := sols.any (fun a' => a' v == b && pins.all (fun u => a' u == a u))
          if exists_ then
            acc := { acc with instances := acc.instances + 1 }
            match runRepair mode C φ.nVars a pins v b with
            | none => acc := { acc with failedStuck := acc.failedStuck + 1 }
            | some a' =>
              if C.all (satClauseB a') && a' v == b && pins.all (fun u => a' u == a u) then
                acc := { acc with repaired := acc.repaired + 1 }
              else
                acc := { acc with failedWrong := acc.failedWrong + 1 }
  return (rng, acc)

def reportRAcc (label : String) (x : RAcc) : IO Unit := do
  IO.println s!"  {label}: formulas={x.formulas} instances={x.instances} \
repaired={x.repaired} STUCK={x.failedStuck} WRONG={x.failedWrong}"

/-- `lake exe cnfmap --flipscope [cases] [seed] [nvMin] [nvSpan] [solCap] [pinTries]` —
the constructive repair, inside and outside the bounded-scope class, with the
Tseitin families as the control that must fail. -/
def runFlipScope (cases seed nvMin nvSpan solCap pinTries K : Nat) : IO UInt32 := do
  IO.println s!"--- the constructive repair vs the bounded-scope class: cases={cases} \
seed={seed} vars={nvMin}..{nvMin + nvSpan - 1} K={K} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut inEar : RAcc := {}
  let mut outEar : RAcc := {}
  let mut inFirst : RAcc := {}
  let mut outFirst : RAcc := {}
  let mut inRow : RAcc := {}
  let mut outRow : RAcc := {}
  let mut inRed : RAcc := {}
  let mut outRed : RAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let inClass := AbsSat.GraphMap.CnfHypergraph.boundedScopeB φ K
        -- the same rng start for each mode, so the three see the same triples
        let (_, accEar) := scoreFormula φ .ear solCap pinTries rng
        let (_, accFirst) := scoreFormula φ .first solCap pinTries rng
        let (r4, accRow) := scoreFormula φ .row solCap pinTries rng
        let (_, accRed) := scoreFormula φ .reduce solCap pinTries rng
        rng := r4
        if inClass then
          inEar := inEar.add accEar
          inFirst := inFirst.add accFirst
          inRow := inRow.add accRow
          inRed := inRed.add accRed
        else
          outEar := outEar.add accEar
          outFirst := outFirst.add accFirst
          outRow := outRow.add accRow
          outRed := outRed.add accRed
  IO.println "by VARIABLE, GYO ear order:"
  reportRAcc "in the class    " inEar
  reportRAcc "outside it      " outEar
  IO.println "by VARIABLE, leftmost first:"
  reportRAcc "in the class    " inFirst
  reportRAcc "outside it      " outFirst
  IO.println "by ROW (the unit the machine moves):"
  reportRAcc "in the class    " inRow
  reportRAcc "outside it      " outRow
  IO.println "by ROW, after the semi-join reducer (arc consistency):"
  reportRAcc "in the class    " inRed
  reportRAcc "outside it      " outRed
  IO.println "control — the Tseitin families (all outside the class), reduced:"
  let mut ctl : RAcc := {}
  for (name, nV, edges) in [("K4", 4, k4), ("K3,3", 6, k33), ("prism", 6, prism)] do
    for odd in [true, false] do
      match tseitin nV edges odd with
      | none => pure ()
      | some φ =>
        let inClass := AbsSat.GraphMap.CnfHypergraph.boundedScopeB φ K
        let (r6, acc) := scoreFormula φ .reduce solCap pinTries rng
        rng := r6
        ctl := ctl.add acc
        IO.println s!"    {name} odd={odd}: inClass={inClass} instances={acc.instances} \
repaired={acc.repaired} STUCK={acc.failedStuck}"
  reportRAcc "control total   " ctl
  pure 0

-- ------------------------------------------------------------
-- The pure-model reducer, measured against brute force
-- ------------------------------------------------------------

/-! This band runs the reducer **of the model** — `CnfReducer.reduce`, the one
the theorems are about — rather than a second implementation, and asks two
questions of every clause prefix.

*Does it ever empty a relation of a satisfiable prefix?* It must not, and
`CnfReducer.reduce_ne_nil_of_sat` proves it must not, so a non-zero count here
would mean the definitions do not say what the theorems think they say.

*Does an empty relation catch every unsatisfiable prefix?* In general no —
arc consistency is not a decision procedure. **Inside the bounded-scope class
it should**, and that is exactly what the next piece has to prove. -/

structure DAcc where
  prefixes : Nat := 0
  sat : Nat := 0
  emptyOnSat : Nat := 0
  missedUnsat : Nat := 0

def DAcc.add (x y : DAcc) : DAcc :=
  { prefixes := x.prefixes + y.prefixes, sat := x.sat + y.sat,
    emptyOnSat := x.emptyOnSat + y.emptyOnSat, missedUnsat := x.missedUnsat + y.missedUnsat }

def scoreReducer (φ : Cnf) : DAcc := Id.run do
  let mut acc : DAcc := {}
  let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
  for m in [0:φ.clauses.length + 1] do
    let C := φ.clauses.take m
    let rels := AbsSat.GraphMap.CnfReducer.reduce (AbsSat.GraphMap.CnfReducer.initRels C)
    let emptied := rels.any (fun cr => cr.2.isEmpty)
    let satisfiable := alls.any (fun a => C.all (satClauseB a))
    acc := { acc with prefixes := acc.prefixes + 1 }
    if satisfiable then
      acc := { acc with sat := acc.sat + 1 }
      if emptied then acc := { acc with emptyOnSat := acc.emptyOnSat + 1 }
    else
      if !emptied then acc := { acc with missedUnsat := acc.missedUnsat + 1 }
  return acc

/-- `lake exe cnfmap --reducer [cases] [seed] [nvMin] [nvSpan] [K]` -/
def runReducer (cases seed nvMin nvSpan K : Nat) : IO UInt32 := do
  IO.println s!"--- the model's reducer vs brute force: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} K={K} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut inAcc : DAcc := {}
  let mut outAcc : DAcc := {}
  let mut inF := 0
  let mut outF := 0
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let acc := scoreReducer φ
        if AbsSat.GraphMap.CnfHypergraph.boundedScopeB φ K then
          inAcc := inAcc.add acc
          inF := inF + 1
        else
          outAcc := outAcc.add acc
          outF := outF + 1
  IO.println s!"  in the class : formulas={inF} prefixes={inAcc.prefixes} (sat={inAcc.sat}) \
EMPTIED-A-SAT-PREFIX={inAcc.emptyOnSat} unsat-not-caught={inAcc.missedUnsat}"
  IO.println s!"  outside it   : formulas={outF} prefixes={outAcc.prefixes} (sat={outAcc.sat}) \
EMPTIED-A-SAT-PREFIX={outAcc.emptyOnSat} unsat-not-caught={outAcc.missedUnsat}"
  IO.println "control — the Tseitin families:"
  for (name, nV, edges) in [("K4", 4, k4), ("K3,3", 6, k33), ("prism", 6, prism)] do
    for odd in [true, false] do
      match tseitin nV edges odd with
      | none => pure ()
      | some φ =>
        let acc := scoreReducer φ
        IO.println s!"    {name} odd={odd}: prefixes={acc.prefixes} (sat={acc.sat}) \
EMPTIED-A-SAT-PREFIX={acc.emptyOnSat} unsat-not-caught={acc.missedUnsat}"
  pure 0

-- ------------------------------------------------------------
-- The choosing step: how much the base case covers, and what is left
-- ------------------------------------------------------------

/-! `CnfSelection` proves the obligation where the reducer leaves one row per
relation — the no-choice case, the same base case v19 and v40 discharged for
the machine. What is left is the step: pin one relation to one of its rows,
re-reduce, and never empty anything.

Two forms, and the difference is the one v41 already drew for the machine:
`∃` a good row per relation (`PickSome`) is what the descent needs; `∀` rows
good (`PickValid`) is stronger and would be more comfortable. This band
measures both. -/

open AbsSat.GraphMap.CnfReducer in
def pinAt (rels : Rels) (i : Nat) (r : Int) : Rels :=
  match rels[i]? with
  | none => rels
  | some cr => rels.set i (cr.1, [r])

structure PAcc where
  prefixes : Nat := 0
  pinnedAll : Nat := 0
  instances : Nat := 0
  someGood : Nat := 0
  allGood : Nat := 0
  descents : Nat := 0
  descentOk : Nat := 0
  descentFailOnSat : Nat := 0
  descentOkOnUnsat : Nat := 0

def PAcc.add (x y : PAcc) : PAcc :=
  { prefixes := x.prefixes + y.prefixes, pinnedAll := x.pinnedAll + y.pinnedAll,
    instances := x.instances + y.instances, someGood := x.someGood + y.someGood,
    allGood := x.allGood + y.allGood, descents := x.descents + y.descents,
    descentOk := x.descentOk + y.descentOk,
    descentFailOnSat := x.descentFailOnSat + y.descentFailOnSat,
    descentOkOnUnsat := x.descentOkOnUnsat + y.descentOkOnUnsat }

open AbsSat.GraphMap.CnfReducer in
/-- The greedy descent: pin the first row of the first relation that still
offers a choice, re-reduce, repeat. `true` when it reaches one row per relation
with nothing emptied. -/
def descend : Nat → Rels → Bool
  | 0, _ => false
  | n + 1, rels =>
    match (List.range rels.length).find? (fun i =>
      match rels[i]? with
      | some cr => cr.2.length > 1
      | none => false) with
    | none => true
    | some i =>
      match rels[i]?.bind (fun cr => cr.2.head?) with
      | none => false
      | some r =>
        let rels' := reduce (pinAt rels i r)
        if rels'.any (fun q => q.2.isEmpty) then false else descend n rels'

open AbsSat.GraphMap.CnfReducer in
def scorePick (φ : Cnf) : PAcc := Id.run do
  let mut acc : PAcc := {}
  for m in [0:φ.clauses.length + 1] do
    let C := φ.clauses.take m
    let rels := reduce (initRels C)
    if rels.all (fun cr => !cr.2.isEmpty) then
      acc := { acc with prefixes := acc.prefixes + 1 }
      if rels.all (fun cr => cr.2.length == 1) then
        acc := { acc with pinnedAll := acc.pinnedAll + 1 }
      for i in [0:rels.length] do
        match rels[i]? with
        | none => pure ()
        | some cr =>
          if cr.2.length > 1 then
            acc := { acc with instances := acc.instances + 1 }
            let good := cr.2.filter (fun r =>
              (reduce (pinAt rels i r)).all (fun q => !q.2.isEmpty))
            if good.length > 0 then acc := { acc with someGood := acc.someGood + 1 }
            if good.length == cr.2.length then acc := { acc with allGood := acc.allGood + 1 }
      -- the full greedy descent, and what it means against brute force
      let ok := descend (totalRows rels + 1) rels
      let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
      let satisfiable := alls.any (fun a => C.all (satClauseB a))
      acc := { acc with descents := acc.descents + 1 }
      if ok then acc := { acc with descentOk := acc.descentOk + 1 }
      if ok && !satisfiable then acc := { acc with descentOkOnUnsat := acc.descentOkOnUnsat + 1 }
      if !ok && satisfiable then acc := { acc with descentFailOnSat := acc.descentFailOnSat + 1 }
  return acc

/-- `lake exe cnfmap --pickstep [cases] [seed] [nvMin] [nvSpan] [K]` -/
def runPickStep (cases seed nvMin nvSpan K : Nat) : IO UInt32 := do
  IO.println s!"--- the choosing step after the reducer: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} K={K} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut inAcc : PAcc := {}
  let mut outAcc : PAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let acc := scorePick φ
        if AbsSat.GraphMap.CnfHypergraph.boundedScopeB φ K then inAcc := inAcc.add acc
        else outAcc := outAcc.add acc
  let line := fun (name : String) (x : PAcc) =>
    IO.println s!"  {name}: prefixes={x.prefixes} pinned-by-the-reducer={x.pinnedAll} \
choices={x.instances} SOME-row-works={x.someGood} EVERY-row-works={x.allGood}\n\
      descents={x.descents} reached-a-selection={x.descentOk} \
FAILED-ON-A-SAT-PREFIX={x.descentFailOnSat} succeeded-on-UNSAT={x.descentOkOnUnsat}"
  line "in the class " inAcc
  line "outside it   " outAcc
  IO.println "control — the Tseitin families:"
  for (name, nV, edges) in [("K4", 4, k4), ("K3,3", 6, k33), ("prism", 6, prism)] do
    for odd in [true, false] do
      match tseitin nV edges odd with
      | none => pure ()
      | some φ =>
        let x := scorePick φ
        IO.println s!"    {name} odd={odd}: prefixes={x.prefixes} choices={x.instances} \
SOME={x.someGood} EVERY={x.allGood} descents={x.descents} reached={x.descentOk} \
FAIL-ON-SAT={x.descentFailOnSat} OK-ON-UNSAT={x.descentOkOnUnsat}"
  pure 0

-- ------------------------------------------------------------
-- The band v74 asked for: the machine's surviving rows vs the reducer's
-- ------------------------------------------------------------

/-! v71–v73 built a reducer over clause relations and compared it to the
machine **in prose only**. This band does it with numbers, on real runs.

At every clause step of a real execution there are three sets of rows:

* what **the machine** leaves alive — the keys at that step whose state is
  still valid;
* what **the reducer** leaves alive — the rows of that clause in
  `CnfReducer.reduce` of the prefix seen so far;
* the **truth** — the rows some assignment satisfying that prefix actually
  uses, by brute force.

`lost` counts rows the truth uses and the procedure killed: it must be zero for
both (that is conservation, proved on the reducer side). `spurious` counts rows
kept that no solution uses. And `extra` counts where the two procedures
disagree, which is the question v74 left open. -/

def sortU (l : List Int) : List Int :=
  (l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).mergeSort (fun a b => a ≤ b)

def minusL (a b : List Int) : List Int := (sortU a).filter (fun x => !b.contains x)

structure BAcc where
  steps : Nat := 0
  agree : Nat := 0
  machExtra : Nat := 0
  redExtra : Nat := 0
  machSpurious : Nat := 0
  redSpurious : Nat := 0
  machLost : Nat := 0
  redLost : Nat := 0

def BAcc.add (x y : BAcc) : BAcc :=
  { steps := x.steps + y.steps, agree := x.agree + y.agree,
    machExtra := x.machExtra + y.machExtra, redExtra := x.redExtra + y.redExtra,
    machSpurious := x.machSpurious + y.machSpurious, redSpurious := x.redSpurious + y.redSpurious,
    machLost := x.machLost + y.machLost, redLost := x.redLost + y.redLost }

open AbsSat.GraphMap.CnfReducer in
def scoreBand (φ : Cnf) (tri : Bool) : BAcc := Id.run do
  let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
  let steps := (stepCount φ - 1).toNat
  let mut line := pureInit φ
  let mut acc : BAcc := {}
  for s in [0:steps + 1] do
    let k : Int := (s : Int)
    if litBlock φ < k && k < fusionTop φ then
      let j := (k - litBlock φ - 1).toNat
      match φ.clauses[j]? with
      | none => pure ()
      | some cj =>
        -- the machine's surviving rows at this clause step
        let machRows := (line.filter (fun kv => kv.1.step == k && isValid kv.2)).map
          (fun kv => kv.1.index)
        -- the reducer's surviving rows for the same clause, on the prefix seen
        let C := φ.clauses.take (j + 1)
        let rels := reduce (initRels C)
        let redRows := match rels[j]? with | some cr => cr.2 | none => []
        -- the truth
        let truth := allRows.filter (fun r =>
          alls.any (fun a => C.all (satClauseB a) && rowOfAssign a cj == r))
        acc := { acc with steps := acc.steps + 1 }
        if (sortU machRows) == (sortU redRows) then acc := { acc with agree := acc.agree + 1 }
        acc := { acc with
          machExtra := acc.machExtra + (minusL machRows redRows).length,
          redExtra := acc.redExtra + (minusL redRows machRows).length,
          machSpurious := acc.machSpurious + (minusL machRows truth).length,
          redSpurious := acc.redSpurious + (minusL redRows truth).length,
          machLost := acc.machLost + (minusL truth machRows).length,
          redLost := acc.redLost + (minusL truth redRows).length }
    if s < steps then line := if tri then pureAdvanceTri φ line else pureAdvance φ line
  return acc

def reportBand (name : String) (x : BAcc) : IO Unit := do
  IO.println s!"  {name}: clause steps={x.steps} same-set={x.agree} \
(machine-only rows={x.machExtra}, reducer-only rows={x.redExtra})"
  IO.println s!"    vs the truth: machine spurious={x.machSpurious} LOST={x.machLost} | \
reducer spurious={x.redSpurious} LOST={x.redLost}"

/-- `lake exe cnfmap --band [cases] [seed] [nvMin] [nvSpan] [K]` -/
def runBand (cases seed nvMin nvSpan K : Nat) : IO UInt32 := do
  IO.println s!"--- the machine's surviving rows vs the reducer's: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} K={K} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut inOrig : BAcc := {}
  let mut outOrig : BAcc := {}
  let mut inTri : BAcc := {}
  let mut outTri : BAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        let o := scoreBand φ false
        let t := scoreBand φ true
        if AbsSat.GraphMap.CnfHypergraph.boundedScopeB φ K then
          inOrig := inOrig.add o; inTri := inTri.add t
        else
          outOrig := outOrig.add o; outTri := outTri.add t
  IO.println "ORIGINAL machine:"
  reportBand "in the class " inOrig
  reportBand "outside it   " outOrig
  IO.println "machine with the TRIANGLE pass:"
  reportBand "in the class " inTri
  reportBand "outside it   " outTri
  IO.println "control — the Tseitin families (original machine):"
  for (name, nV, edges) in [("K4", 4, k4), ("K3,3", 6, k33), ("prism", 6, prism)] do
    for odd in [true, false] do
      match tseitin nV edges odd with
      | none => pure ()
      | some φ =>
        let x := scoreBand φ false
        IO.println s!"    {name} odd={odd}: steps={x.steps} same-set={x.agree} \
mach-only={x.machExtra} red-only={x.redExtra} machLOST={x.machLost} redLOST={x.redLost}"
  pure 0

-- ------------------------------------------------------------
-- The fabric at the clause steps
-- ------------------------------------------------------------

/-! v65 measured the greatest fabric inside `owners(r)` at **full length**, on
the reader's own choices. The route to `PairwiseOwned` that is still alive
needs it somewhere else: at the **clause steps**, the intermediate states where
the filter narrows the tables, and it needs a different property.

Size is not what matters — **coverage** is. `Closed`/`CoreCovers` (v44) asks
that the self-sustaining set reach *every* step. A fabric that is small but
covers every step still carries a chain; one that is large but empty at some
step carries nothing. So this band reports coverage first, and a fabric that
misses a step is the counterexample that would kill the route. -/

structure FCell where
  members : Nat
  kept : Nat
  covers : Bool
  hasSelf : Bool
  entries : Nat
  entriesKept : Nat

def fabricCover (g : GPathM) (rn : PNodeM) : FCell :=
  let S0 := g.nodes.filter (fun n => rn.owners.contains n.id)
  let T0 : Tab := S0.map (fun n => (n.id, n.owners.filter (fun v => rn.owners.contains v &&
    (g.nodes.any (fun m => m.id == v)))))
  let Tf := gfabric g T0 1000
  { members := S0.length, kept := Tf.length,
    covers := (intRange 0 (g.current_step - 1)).all (fun k => Tf.any (fun e => e.1.id.step == k)),
    hasSelf := Tf.any (fun e => e.1 == rn.id),
    entries := (T0.map (·.2.length)).foldl (· + ·) 0,
    entriesKept := (Tf.map (·.2.length)).foldl (· + ·) 0 }

structure FCAcc where
  states : Nat := 0
  nodes : Nat := 0
  full : Nat := 0
  covers : Nat := 0
  missesAStep : Nat := 0
  losesSelf : Nat := 0
  entries : Nat := 0
  entriesKept : Nat := 0

def FCAcc.add (x y : FCAcc) : FCAcc :=
  { states := x.states + y.states, nodes := x.nodes + y.nodes, full := x.full + y.full,
    covers := x.covers + y.covers, missesAStep := x.missesAStep + y.missesAStep,
    losesSelf := x.losesSelf + y.losesSelf, entries := x.entries + y.entries,
    entriesKept := x.entriesKept + y.entriesKept }

def scoreFabricClause (φ : Cnf) (sym : Bool) : FCAcc := Id.run do
  let steps := (stepCount φ - 1).toNat
  let mut line := pureInit φ
  let mut acc : FCAcc := {}
  for s in [0:steps + 1] do
    let k : Int := (s : Int)
    if litBlock φ < k && k < fusionTop φ then
      for kv in line do
        let g := kv.2
        if isValid g then
          acc := { acc with states := acc.states + 1 }
          for n in g.nodes do
            let t := fabricCover g n
            acc := { acc with nodes := acc.nodes + 1, entries := acc.entries + t.entries, entriesKept := acc.entriesKept + t.entriesKept }
            if t.members == t.kept then acc := { acc with full := acc.full + 1 }
            if t.covers then acc := { acc with covers := acc.covers + 1 }
            else acc := { acc with missesAStep := acc.missesAStep + 1 }
            if !t.hasSelf then acc := { acc with losesSelf := acc.losesSelf + 1 }
    if s < steps then line := if sym then pureAdvanceSym φ line else pureAdvance φ line
  return acc

/-- `lake exe cnfmap --fabclause [cases] [seed] [nvMin] [nvSpan]` -/
def runFabricClause (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- the fabric inside owners(n) at the CLAUSE steps: cases={cases} \
seed={seed} vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut orig : FCAcc := {}
  let mut symm : FCAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ =>
      if AbsSat.Cnf.Dimacs.wfB φ then
        orig := orig.add (scoreFabricClause φ false)
        symm := symm.add (scoreFabricClause φ true)
  let line := fun (name : String) (x : FCAcc) =>
    IO.println s!"  {name}: states={x.states} nodes={x.nodes} fabric=ALL owners={x.full} \
COVERS-every-step={x.covers} MISSES-a-step={x.missesAStep} loses-itself={x.losesSelf} \
entries {x.entriesKept}/{x.entries}"
  line "original machine " orig
  line "symmetric machine" symm
  IO.println "control — the Tseitin families:"
  for (name, nV, edges) in [("K4", 4, k4), ("K3,3", 6, k33), ("prism", 6, prism)] do
    for odd in [true, false] do
      match tseitin nV edges odd with
      | none => pure ()
      | some φ =>
        let x := scoreFabricClause φ true
        IO.println s!"    {name} odd={odd}: states={x.states} nodes={x.nodes} \
ALL={x.full} COVERS={x.covers} MISSES={x.missesAStep} loses-itself={x.losesSelf} \
entries {x.entriesKept}/{x.entries}"
  pure 0

/-! ### Is `PinNonEmpty` anything more than `isValid`?

v81 proved `PinNonEmpty g q → isValid (filterAll g [q.id])`. If the converse
also holds, the reduction is a restatement and the fabric buys nothing. This
band decides it: for every owner `q` at a step that still offers a choice,
compute the greatest fabric among the nodes compatible with pinning `q`, and
compare "that fabric is non-empty" against "the machine says the pinned state
is valid". -/

def compatNodes (g : GPathM) (q : PathNodeId) : List PNodeM :=
  g.nodes.filter (fun n => n.id.id.step != q.id.step || n.id.id == q.id)

/-- The greatest fabric among the nodes compatible with the pin. -/
def pinFabricNonEmpty (g : GPathM) (q : PathNodeId) : Bool :=
  let S0 := compatNodes g q
  let ids := S0.map (·.id)
  let T0 : Tab := S0.map (fun n => (n.id, n.owners.filter (fun v => ids.contains v)))
  !(gfabric g T0 1000).isEmpty

structure TAcc where
  pins : Nat := 0
  bothYes : Nat := 0
  bothNo : Nat := 0
  fabYesValidNo : Nat := 0
  fabNoValidYes : Nat := 0

def TAcc.add (x y : TAcc) : TAcc :=
  { pins := x.pins + y.pins, bothYes := x.bothYes + y.bothYes, bothNo := x.bothNo + y.bothNo,
    fabYesValidNo := x.fabYesValidNo + y.fabYesValidNo,
    fabNoValidYes := x.fabNoValidYes + y.fabNoValidYes }

def scoreTauto (φ : Cnf) : TAcc := Id.run do
  let steps := (stepCount φ - 1).toNat
  let mut line := pureInit φ
  let mut acc : TAcc := {}
  for s in [0:steps + 1] do
    let k : Int := (s : Int)
    if litBlock φ < k && k < fusionTop φ then
      for kv in line do
        let g := kv.2
        if isValid g then
          for j in intRange 0 (g.current_step - 1) do
            if PickInduction.choiceAt g j then
              for q in ownersAt g.gowners j do
                let fab := pinFabricNonEmpty g q
                let val := isValid (filterAll g [q.id])
                acc := { acc with pins := acc.pins + 1 }
                if fab && val then acc := { acc with bothYes := acc.bothYes + 1 }
                if !fab && !val then acc := { acc with bothNo := acc.bothNo + 1 }
                if fab && !val then acc := { acc with fabYesValidNo := acc.fabYesValidNo + 1 }
                if !fab && val then acc := { acc with fabNoValidYes := acc.fabNoValidYes + 1 }
    if s < steps then line := pureAdvanceSym φ line
  return acc

/-- `lake exe cnfmap --tauto [cases] [seed] [nvMin] [nvSpan]` -/
def runTauto (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- is PinNonEmpty more than isValid? cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : TAcc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ => if AbsSat.Cnf.Dimacs.wfB φ then acc := acc.add (scoreTauto φ)
  IO.println s!"  pins examined                 = {acc.pins}"
  IO.println s!"  fabric YES and valid YES      = {acc.bothYes}"
  IO.println s!"  fabric NO  and valid NO       = {acc.bothNo}"
  IO.println s!"  fabric YES but NOT valid      = {acc.fabYesValidNo}"
  IO.println s!"  NO fabric but VALID (the gap) = {acc.fabNoValidYes}"
  pure 0

/-! ### P3 itself, measured

v77 computed the greatest fabric inside `owners(r)` and found it always covers.
But that is the **unpinned** question. What P3 needs is the fabric inside
`owners(r)` *and* agreeing with the clause's three requirements — a **triple**
intersection at every step, which is exactly the shape v70 found triple gaps
in. This band asks P3's own question. -/

def compatWith (reqs : List NodeId) (p : PathNodeId) : Bool :=
  reqs.all (fun r => p.id.step != r.step || p.id == r)

/-- The greatest fabric inside `owners(rn)` whose members agree with `reqs`:
members kept, whether it covers every step, whether it still holds `r`. -/
def pinnedFabric (g : GPathM) (rn : PNodeM) (reqs : List NodeId) : Nat × Bool × Bool :=
  let S0 := g.nodes.filter (fun n => rn.owners.contains n.id && compatWith reqs n.id)
  let ids := S0.map (·.id)
  let T0 : Tab := S0.map (fun n => (n.id, n.owners.filter (fun v => ids.contains v)))
  let Tf := gfabric g T0 1000
  (Tf.length,
   (intRange 0 (g.current_step - 1)).all (fun k => Tf.any (fun e => e.1.id.step == k)),
   Tf.any (fun e => e.1 == rn.id))

structure P3Acc where
  filters : Nat := 0
  survivors : Nat := 0
  covers : Nat := 0
  missesAStep : Nat := 0
  losesR : Nat := 0
  empties : Nat := 0

def P3Acc.add (x y : P3Acc) : P3Acc :=
  { filters := x.filters + y.filters, survivors := x.survivors + y.survivors,
    covers := x.covers + y.covers, missesAStep := x.missesAStep + y.missesAStep,
    losesR := x.losesR + y.losesR, empties := x.empties + y.empties }

def scoreP3 (φ : Cnf) : P3Acc := Id.run do
  let steps := (stepCount φ - 1).toNat
  let mut line := pureInit φ
  let mut acc : P3Acc := {}
  for _ in [0:steps] do
    for kv in line do
      let g := kv.2
      if isValid g then
        for d in mapSons φ kv.1.step kv.1.index do
          if litBlock φ < d.step && d.step < fusionTop φ then
            let reqs := reqOfCnf φ d
            let h := filterAll g reqs
            if isValid h then
              acc := { acc with filters := acc.filters + 1 }
              for n in h.nodes do
                match g.node? n.id with
                | none => pure ()
                | some rn =>
                  acc := { acc with survivors := acc.survivors + 1 }
                  let t := pinnedFabric g rn reqs
                  if t.1 == 0 then acc := { acc with empties := acc.empties + 1 }
                  if t.2.1 then acc := { acc with covers := acc.covers + 1 }
                  else acc := { acc with missesAStep := acc.missesAStep + 1 }
                  if !t.2.2 then acc := { acc with losesR := acc.losesR + 1 }
    line := pureAdvanceSym φ line
  return acc

/-- `lake exe cnfmap --p3 [cases] [seed] [nvMin] [nvSpan]` -/
def runP3 (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- P3 itself: the fabric inside owners(r) AND agreeing with the pins: \
cases={cases} seed={seed} vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut acc : P3Acc := {}
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
    match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
    | .error _ => pure ()
    | .ok φ => if AbsSat.Cnf.Dimacs.wfB φ then acc := acc.add (scoreP3 φ)
  IO.println s!"  clause filters (valid)            = {acc.filters}"
  IO.println s!"  survivors r examined              = {acc.survivors}"
  IO.println s!"    pinned fabric COVERS every step = {acc.covers}"
  IO.println s!"    MISSES a step                   = {acc.missesAStep}"
  IO.println s!"    is EMPTY                        = {acc.empties}"
  IO.println s!"    does not contain r              = {acc.losesR}"
  pure 0

end AbsSat.GraphMap.SymCampaign
