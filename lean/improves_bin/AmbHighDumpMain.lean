import AbsSatBin.GraphPath.Model.AmbHighCore
import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.Cnf.Dimacs

/-! `lake exe ambhigh-dump f.cnf` — cross-checks the first `TriPin` failure that `ambhigh-probe`
reports, independently of the probe's loop:

* the pins that lead to the state, `k`, `x`, the failing pair `(y, w)` and step `l`;
* the three tables at step `l` and their intersection, printed in full;
* the kernel clauses the proofs use (symmetry, the pair rule), rechecked on the whole state;
* the semantics: every solution of `φ` that agrees with the pins and with `x`, and whether its path
  passes through `y`, `w`, or both. A genuine failure must have **no** solution through both, since a
  solution's node at step `l` would lie in all three tables;
* what the pin at `x` does to `y`, `w` and the link between them. -/

open AbsSatBin.Utils.Alias AbsSatBin.Cnf AbsSatBin.GraphPath.Model AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.PureDriver AbsSatBin.GraphPath.Model.DriverBin

def showP (p : PathNodeId) : String :=
  let o : Option NodeId → String := fun | none => "_" | some n => s!"{n.step}.{n.index}"
  s!"[{p.id.step}.{p.id.index}|{o p.parent_id}|{o p.gparent_id}]"

def ownersB (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.owners | none => []

/-- The path node a solution goes through at step `s` (id plus its two-step window). -/
def solPid (φ : Cnf) (a : Assign) (s : Int) : PathNodeId :=
  { id := selOfAssign φ a s
    parent_id := if s ≤ 0 then none else some (selOfAssign φ a (s - 1))
    -- idx: the three-step window of a path node (one gpath row per map step, bin map too)
    gparent_id := if s ≤ 1 then none else some (selOfAssign φ a (s - 2)) }

/-- The first `(y, w, l)` where the triple rule fails at `x`. -/
def firstTri (g : GPathM) (x : PathNodeId) : Option (PathNodeId × PathNodeId × Int) := Id.run do
  let some nx := g.node? x | return none
  for ny in g.nodes do
    if !ny.owners.contains x then continue
    for w in ny.owners do
      let some nw := g.node? w | continue
      if !nw.owners.contains x then continue
      for i in List.range g.current_step.toNat do
        let l : Int := i
        if !(ny.owners.any fun r => r.id.step == l && nw.owners.contains r && nx.owners.contains r) then
          return some (ny.id, w, l)
  return none

/-- Depth-first over every reader branch: the first state, pins, `k`, `x` with a failure. -/
partial def find (g : GPathM) (ps : List NodeId) :
    Option (GPathM × List NodeId × Int × PathNodeId × PathNodeId × PathNodeId × Int) := Id.run do
  if !isValid g then return none
  let some k := firstChoice g | return none
  for x in ownersAt g.gowners k do
    if let some (y, w, l) := firstTri g x then return some (g, ps, k, x, y, w, l)
  for d in (ownersAt g.gowners k).map (·.id) |>.eraseDups do
    let g' := filterAll g [d]
    if isValid g' then
      if let some r := find g' (d :: ps) then return some r
  return none

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.println "uso: ambhigh-dump f.cnf"; return 1
  let .ok φ := Dimacs.parse (← IO.FS.lines path).toList | IO.println "parse error"; return 1
  let mut found := none
  for kv in pureRun φ do
    if found.isNone then found := find (filterAll kv.2 []) []
  let some (g, ps, k, x, y, w, l) := found | IO.println "sin fallos de TriPin"; return 0
  IO.println s!"pins (último primero) = {ps.map fun d => s!"{d.step}.{d.index}"}  k={k}  cs={g.current_step}"
  IO.println s!"x={showP x}  y={showP y}  w={showP w}  l={l}"
  let oy := ownersB g y; let ow := ownersB g w; let ox := ownersB g x
  IO.println s!"w ∈ tabla(y): {oy.contains w}   x ∈ tabla(y): {oy.contains x}   x ∈ tabla(w): {ow.contains x}"
  let atL := fun (o : List PathNodeId) => (o.filter (·.id.step == l)).map showP
  IO.println s!"tabla(y)@{l} = {atL oy}"
  IO.println s!"tabla(w)@{l} = {atL ow}"
  IO.println s!"tabla(x)@{l} = {atL ox}"
  IO.println s!"y∩w@{l} = {atL (oy.filter ow.contains)}   y∩x@{l} = {atL (oy.filter ox.contains)}   w∩x@{l} = {atL (ow.filter ox.contains)}"
  -- kernel clauses on the whole state
  let mut symBad := 0
  let mut pairBad := 0
  for n in g.nodes do
    for v in n.owners do
      match g.node? v with
      | none => symBad := symBad + 1
      | some nv =>
        if !nv.owners.contains n.id then symBad := symBad + 1
        for i in List.range g.current_step.toNat do
          let s : Int := i
          if !(n.owners.any fun r => r.id.step == s && nv.owners.contains r) then pairBad := pairBad + 1
  IO.println s!"kernel: simetría rota = {symBad}, regla de parejas rota = {pairBad}, nodos = {g.nodes.length}"
  -- semantics
  let sols := (List.range (2 ^ φ.nVars)).filterMap fun m =>
    let a : Assign := fun v => m.testBit v
    if satB a φ then some (m, a) else none
  let agree := sols.filter fun (_, a) => (x.id :: ps).all fun p => selOfAssign φ a p.step == p
  IO.println s!"soluciones = {sols.length}; de acuerdo con pins + x = {agree.length}"
  let mut both := 0
  for (m, a) in agree do
    let py := solPid φ a y.id.step; let pw := solPid φ a w.id.step; let pl := solPid φ a l
    let iy := py == y; let iw := pw == w
    if iy && iw then both := both + 1
    IO.println s!"  sol m={m}: pasa por y={iy} w={iw}; su nodo en {l} = {showP pl}; en tablas y/w/x = {oy.contains pl}/{ow.contains pl}/{ox.contains pl}"
  IO.println s!"soluciones por x, y y w a la vez = {both}"
  -- the pin
  let g' := filterAll g [x.id]
  IO.println s!"tras pinchar x: válido={isValid g'}  y vivo={(g'.node? y).isSome}  w vivo={(g'.node? w).isSome}  w ∈ tabla(y)={(ownersB g' y).contains w}"
  return 0
