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

end AbsSat.GraphMap.SymCampaign
