-- lean_project/AbsSat/GraphMap/SymCampaign.lean
import AbsSat.GraphMap.CnfMapDiff
import AbsSat.GraphPath.Model.SymReview

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

end AbsSat.GraphMap.SymCampaign
