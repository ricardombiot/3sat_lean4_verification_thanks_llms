import AbsSatBin.GraphPath.Model.PinChainBin
import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.Cnf.Dimacs

/-! `lake exe otherbit-probe [--chain] [--cap N] f1.cnf …` — measures the reader's one open
obligation on the states the reader can visit.

From each starting state `filterAll kv.2 []` it walks **every** `ReadFirst` branch (every valid
pin at `firstChoice`, not only the one `tryPins` takes), up to `--cap` states per start, keeping the
list of pins (`OtherBitSem.ReadPins`).

* default: **`OtherBitSem.OtherBitSem`**, by brute force over the solutions of `φ`. A failure is a
  valid pin `q` at a state where some solution agrees with the pins but none agrees with the pins
  and `q`.
* `--chain`: **`PinChainBin.OtherBit`**, searching a `ChainSound` through `q.id` step by step (the
  exact Lean definition; much slower).

Read-only: nothing is changed in the machine. -/

open AbsSatBin.Utils.Alias AbsSatBin.Cnf AbsSatBin.GraphPath.Model AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.PureDriver AbsSatBin.GraphPath.Model.DriverBin

def ownersB (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.owners | none => []

def sonsB (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.sons | none => []

/-- Is there a `ChainSound g sel` with `(sel k).id = d` (when `fix = some (k, d)`)? Depth-first,
checking every field of `ChainSound` as soon as its nodes are chosen. `acc` is the chosen prefix. -/
partial def chainFrom (g : GPathM) (fix : Option (Int × NodeId)) (i : Int)
    (acc : Array PathNodeId) : Bool :=
  if i ≥ g.current_step then true
  else (g.line i).any fun n =>
    let p := n.id
    let fixOk := match fix with
      | some (k, d) => i != k || p.id == d
      | none => true
    fixOk && g.gowners.contains p && n.owners.contains p
      && (if i == 0 then p.parent_id == none else p.parent_id != none)
      && (if h : acc.size > 0 then
            let prev := acc[acc.size - 1]
            n.parents.contains prev && (sonsB g prev).contains p
          else true)
      && acc.all (fun r => n.owners.contains r && (ownersB g r).contains p)
      && chainFrom g fix (i + 1) (acc.push p)

structure Stats where
  states : Nat := 0
  witnessed : Nat := 0
  unwitnessed : Nat := 0
  pins : Nat := 0
  validPins : Nat := 0
  fails : Nat := 0
  capped : Bool := false
  firstFail : Option String := none

/-- The obligation holds at this pin? `sols` are the solutions of `φ`. -/
def pinOk (chainMode : Bool) (φ : Cnf) (sols : List Assign) (g : GPathM) (ps : List NodeId)
    (k : Int) (d : NodeId) : Bool :=
  if chainMode then chainFrom g (some (k, d)) 0 #[]
  else sols.any (fun a => (d :: ps).all (fun p => selOfAssign φ a p.step == p))

/-- Does the state have a witness (a solution agreeing with the pins, or a chain)? -/
def witnessed (chainMode : Bool) (φ : Cnf) (sols : List Assign) (g : GPathM) (ps : List NodeId) :
    Bool :=
  if chainMode then chainFrom g none 0 #[]
  else sols.any (fun a => ps.all (fun p => selOfAssign φ a p.step == p))

partial def explore (chainMode : Bool) (φ : Cnf) (sols : List Assign) (cap : Nat) (g : GPathM)
    (ps : List NodeId) (st : Stats) : Stats := Id.run do
  if st.states ≥ cap then return { st with capped := true }
  let mut st := { st with states := st.states + 1 }
  if !isValid g then return st
  let hasW := witnessed chainMode φ sols g ps
  if hasW then st := { st with witnessed := st.witnessed + 1 }
  else st := { st with unwitnessed := st.unwitnessed + 1 }
  match firstChoice g with
  | none => return st
  | some k =>
    let ids := (ownersAt g.gowners k).map (·.id) |>.eraseDups
    for d in ids do
      let g' := filterAll g [d]
      st := { st with pins := st.pins + 1 }
      if isValid g' then
        st := { st with validPins := st.validPins + 1 }
        if hasW && !pinOk chainMode φ sols g ps k d then
          st := { st with fails := st.fails + 1,
                          firstFail := st.firstFail.orElse (fun _ => some s!"k={k} bit={d.index} pins={ps.length}") }
        st := explore chainMode φ sols cap g' (d :: ps) st
    return st

def checkOne (chainMode : Bool) (cap : Nat) (path : String) : IO Nat := do
  let lines := (← IO.FS.lines path).toList
  let name := (System.FilePath.mk path).fileName.getD path
  match Dimacs.parse lines with
  | .error e => IO.println s!"{name}\tSKIP\t{e}"; return 0
  | .ok φ =>
    if φ.clauses.isEmpty then IO.println s!"{name}\tSKIP\tno clauses"; return 0
    let t0 ← IO.monoMsNow
    let sols : List Assign := (List.range (2 ^ φ.nVars)).filterMap (fun m =>
      let a : Assign := fun v => m.testBit v
      if satB a φ then some a else none)
    let r := pureRun φ
    let t1 ← IO.monoMsNow
    let mut st : Stats := {}
    for kv in r do
      st := explore chainMode φ sols cap (filterAll kv.2 []) [] st
    let t2 ← IO.monoMsNow
    IO.println s!"{name}\tsols={sols.length}\tstarts={r.length}\tstates={st.states}\twitnessed={st.witnessed}\tunwitnessed={st.unwitnessed}\tpins={st.pins}\tvalid={st.validPins}\tfails={st.fails}\tcapped={st.capped}\tfirst={st.firstFail.getD "-"}\tmachine_ms={t1 - t0}\tprobe_ms={t2 - t1}"
    return st.fails

def main (args : List String) : IO UInt32 := do
  let chainMode := args.contains "--chain"
  let args := args.filter (· != "--chain")
  let (cap, files) := match args with
    | "--cap" :: n :: rest => (n.toNat!, rest)
    | rest => (2000, rest)
  let mut bad := 0
  for f in files do
    bad := bad + (← checkOne chainMode cap f)
  IO.println s!"fallos ({if chainMode then "OtherBit" else "OtherBitSem"}) = {bad}"
  return 0
