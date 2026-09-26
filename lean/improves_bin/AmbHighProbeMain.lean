import AbsSatBin.GraphPath.Model.AmbHighCore
import AbsSatBin.GraphPath.Model.TriPinCut
import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.Cnf.Dimacs

/-! `lake exe ambhigh-probe [--all] [--cap N] f1.cnf …` — measures `AmbHigh` (and `TriPin`) on the states the
reader can visit.

From each starting state `filterAll kv.2 []` it walks **every** `ReadFirst` branch (every valid pin at
`firstChoice`), up to `--cap` states per file. At each valid state with a first choice `k`, for each
global owner `x` of step `k`, it evaluates the exact Lean definitions:

* `TriPin g x` (`KernelSplit.TriPin`);
* `AmbHigh g k x` (`AmbHighCore.AmbHigh`), and counts the ambiguous pairs above the window.

Per state the reader needs **one** `x` (`AmbHighReader`, `TriPinReader`); the counters `*Both` are the
states where every `x` fails, which is what could break the chain. `dead` counts states where every
pin dies (`NoDeadEnd` fails). Read-only. -/

open AbsSatBin.Utils.Alias AbsSatBin.Cnf AbsSatBin.GraphPath.Model AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.PureDriver AbsSatBin.GraphPath.Model.DriverBin
open AbsSatBin.GraphPath.Model.TriPinCore (excl)
open AbsSatBin.GraphPath.Model.TriPinCut (cx)

/-- The triple `(y, w, x)` shares an entry at step `l`. -/
def shares (ny nw nx : PNodeM) (l : Int) : Bool :=
  ny.owners.any (fun r => r.id.step == l && nw.owners.contains r && nx.owners.contains r)

structure Fail where
  kind : String
  k : Int
  x : Nat
  ys : Int
  ws : Int
  l : Int
  cs : Int
  alive : Bool := false

/-- `(pairs tested, first failure)` of the triple rule at `x`, over pairs selected by `sel` and steps
`l ∈ [lo, current_step)`. -/
def triCheck (g : GPathM) (x : PathNodeId) (sel : PNodeM → Bool) (lo : Int) (kind : String) (k : Int) :
    Nat × Option Fail := Id.run do
  let some nx := g.node? x | return (0, none)
  let mut pairs := 0
  for ny in g.nodes do
    if !(ny.owners.contains x && sel ny) then continue
    for w in ny.owners do
      let some nw := g.node? w | continue
      if !(nw.owners.contains x && sel nw) then continue
      pairs := pairs + 1
      let mut l := lo
      while l < g.current_step do
        if !shares ny nw nx l then
          return (pairs, some { kind, k, x := x.id.index.toNat, ys := ny.id.id.step, ws := nw.id.id.step,
                                l, cs := g.current_step })
        l := l + 1
  return (pairs, none)

/-- First failure of `TriPin₁ g x` (`TriPinCut.TriPin₁`), with the exact test `TriPinCut.cx`. -/
def tri1Check (g : GPathM) (x : PathNodeId) (k : Int) : Option Fail := Id.run do
  let some nx := g.node? x | return none
  for ny in g.nodes do
    if !ny.owners.contains x then continue
    for w in ny.owners do
      let some nw := g.node? w | continue
      if !(nw.owners.contains x && cx g x ny w) then continue
      let mut l : Int := 0
      while l < g.current_step do
        let ok := ny.owners.any (fun r => r.id.step == l && nw.owners.contains r && nx.owners.contains r
          && cx g x ny r && cx g x nw r)
        if !ok then
          return some { kind := "tri1", k, x := x.id.index.toNat, ys := ny.id.id.step,
                        ws := nw.id.id.step, l, cs := g.current_step }
        l := l + 1
  return none

structure Stats where
  allX : Nat := 0
  allXFail : Nat := 0
  allStatesFail : Nat := 0
  firstAll : Option String := none
  tri1Fail : Nat := 0
  tri1FailAlive : Nat := 0
  tri1Both : Nat := 0
  triOkDead : Nat := 0
  tri1OkDead : Nat := 0
  firstTri1 : Option Fail := none
  states : Nat := 0
  choiceStates : Nat := 0
  xs : Nat := 0
  highPairs : Nat := 0
  triFail : Nat := 0
  highFail : Nat := 0
  highFailAlive : Nat := 0
  triBoth : Nat := 0
  highBoth : Nat := 0
  dead : Nat := 0
  capped : Bool := false
  firstTri : Option Fail := none
  firstHigh : Option Fail := none

def showFail : Option Fail → String
  | none => "-"
  | some f => s!"k={f.k} x={f.x} y@{f.ys} w@{f.ws} l={f.l} cs={f.cs} pinVivo={f.alive}"

partial def explore (allMode : Bool) (cap : Nat) (g : GPathM) (st : Stats) : Stats := Id.run do
  if st.states ≥ cap then return { st with capped := true }
  let mut st := { st with states := st.states + 1 }
  if !isValid g then return st
  if allMode then
    -- `AllTriPin₁`: `TriPin₁ g x` for every live node `x`
    let kk := (firstChoice g).getD (-1)
    let mut bad := false
    for nx in g.nodes do
      st := { st with allX := st.allX + 1 }
      if let some f := tri1Check g nx.id kk then
        bad := true
        let msg := s!"k={kk} x@{nx.id.id.step}.{nx.id.id.index} y@{f.ys} w@{f.ws} l={f.l} cs={f.cs}"
        let fa := st.firstAll.orElse (fun _ => some msg)
        st := { st with allXFail := st.allXFail + 1, firstAll := fa }
    if bad then st := { st with allStatesFail := st.allStatesFail + 1 }
  match firstChoice g with
  | none => return st
  | some k =>
    st := { st with choiceStates := st.choiceStates + 1 }
    let xsK := ownersAt g.gowners k
    let mut anyTri := false
    let mut anyHigh := false
    let mut anyTri1 := false
    for x in xsK do
      st := { st with xs := st.xs + 1 }
      let (_, ft) := triCheck g x (fun _ => true) 0 "tri" k
      -- idx: above the three-step window (one gpath row per map step, bin map too)
      let high : PNodeM → Bool := fun n => excl x n == false && n.id.id.step ≥ k + 3
      let (hp, fh) := triCheck g x high (k + 1) "high" k
      let alive := isValid (filterAll g [x.id])
      let ft := ft.map ({ · with alive })
      let fh := fh.map ({ · with alive })
      if fh.isSome && alive then st := { st with highFailAlive := st.highFailAlive + 1 }
      let f1 := (tri1Check g x k).map ({ · with alive })
      match f1 with
      | none =>
        anyTri1 := true
        if !alive then st := { st with tri1OkDead := st.tri1OkDead + 1 }
      | some f =>
        st := { st with tri1Fail := st.tri1Fail + 1, firstTri1 := st.firstTri1.orElse (fun _ => some f) }
        if alive then st := { st with tri1FailAlive := st.tri1FailAlive + 1 }
      if ft.isNone && !alive then st := { st with triOkDead := st.triOkDead + 1 }
      st := { st with highPairs := st.highPairs + hp }
      match ft with
      | none => anyTri := true
      | some f => st := { st with triFail := st.triFail + 1, firstTri := st.firstTri.orElse (fun _ => some f) }
      match fh with
      | none => anyHigh := true
      | some f => st := { st with highFail := st.highFail + 1, firstHigh := st.firstHigh.orElse (fun _ => some f) }
    if !anyTri then st := { st with triBoth := st.triBoth + 1 }
    if !anyHigh then st := { st with highBoth := st.highBoth + 1 }
    if !anyTri1 then st := { st with tri1Both := st.tri1Both + 1 }
    let ids := xsK.map (·.id) |>.eraseDups
    let mut alive := false
    for d in ids do
      let g' := filterAll g [d]
      if isValid g' then
        alive := true
        st := explore allMode cap g' st
    if !alive then st := { st with dead := st.dead + 1 }
    return st

def checkOne (allMode : Bool) (cap : Nat) (path : String) : IO Nat := do
  let lines := (← IO.FS.lines path).toList
  let name := (System.FilePath.mk path).fileName.getD path
  match Dimacs.parse lines with
  | .error e => IO.println s!"{name}\tSKIP\t{e}"; return 0
  | .ok φ =>
    if φ.clauses.isEmpty then IO.println s!"{name}\tSKIP\tno clauses"; return 0
    let t0 ← IO.monoMsNow
    let r := pureRun φ
    let t1 ← IO.monoMsNow
    let mut st : Stats := {}
    for kv in r do
      st := explore allMode cap (filterAll kv.2 []) st
    let t2 ← IO.monoMsNow
    IO.println s!"{name}\tstarts={r.length}\tstates={st.states}\tchoice={st.choiceStates}\txs={st.xs}\thighPairs={st.highPairs}\ttriFail={st.triFail}\thighFail={st.highFail}\thighFailVivo={st.highFailAlive}\ttriBoth={st.triBoth}\thighBoth={st.highBoth}\ttri1Fail={st.tri1Fail}\ttri1FailVivo={st.tri1FailAlive}\ttri1Both={st.tri1Both}\ttriOkDead={st.triOkDead}\ttri1OkDead={st.tri1OkDead}\tdead={st.dead}\tallX={st.allX}\tallXFail={st.allXFail}\tallStatesFail={st.allStatesFail}\tfirstAll={st.firstAll.getD "-"}\tcapped={st.capped}\tfirstTri={showFail st.firstTri}\tfirstHigh={showFail st.firstHigh}\tfirstTri1={showFail st.firstTri1}\tmachine_ms={t1 - t0}\tprobe_ms={t2 - t1}"
    return st.highBoth

def main (args : List String) : IO UInt32 := do
  let allMode := args.contains "--all"
  let args := args.filter (· != "--all")
  let (cap, files) := match args with
    | "--cap" :: n :: rest => (n.toNat!, rest)
    | rest => (2000, rest)
  let mut bad := 0
  for f in files do
    bad := bad + (← checkOne allMode cap f)
  IO.println s!"estados sin ningún x que cumpla AmbHigh = {bad}"
  return 0
