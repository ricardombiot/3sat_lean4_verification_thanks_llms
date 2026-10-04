import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.Cnf.Dimacs

/-! `lake exe clausemix-probe f.cnf v₁ v₂ v₃ j` — the `LineSem` clique test at the third literal of clause
`j` (0-based) for `Q` = the path nodes of `vᵢ = 1` (0-based variables).

* **Per entry across the line** (`LineSem.Owns`): `Q` is a clique and has witnesses at every step of line
  `n+1` (the `L3` step of clause `j`) and of line `n+2`.
* **Inside one state** (`CertClique`): the same test in each state of those lines and of the final line,
  after the review.
* **Semantics**: the solutions of `φ` with `v₁ = v₂ = v₃ = 1`. -/

open AbsSatBin.Utils.Alias AbsSatBin.Cnf AbsSatBin.GraphPath.Model AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphMap.CnfMapBin AbsSatBin.GraphMap.CnfSelBin AbsSatBin.GraphPath.Model.PureDriver

def showP (p : PathNodeId) : String :=
  let o : Option NodeId → String := fun | none => "_" | some n => s!"{n.step}.{n.index}"
  s!"[{p.id.step}.{p.id.index}|{o p.parent_id}|{o p.gparent_id}]"

def ownersB (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  match g.node? p with | some n => n.owners | none => []

def ownsL (line : PureLine) (r q : PathNodeId) : Bool := line.any fun kv => (ownersB kv.2 r).contains q
def allNodes (line : PureLine) : List PathNodeId := (line.flatMap fun kv => kv.2.nodes.map (·.id)).eraseDups

/-- Per-entry test; returns the first step without a witness, if any. -/
def lineTest (line : PureLine) (Q : List PathNodeId) (top : Int) : Bool × Option Int := Id.run do
  let clique := Q.all fun q => Q.all fun s => ownsL line q s
  let ns := allNodes line
  for i in List.range (top.toNat + 1) do
    let l : Int := i
    if !(ns.any fun r => r.id.step == l && Q.all (ownsL line r)) then return (clique, some l)
  return (clique, none)

/-- One-state test (`Clique` and `Wit`). -/
def stateTest (g : GPathM) (Q : List PathNodeId) : Bool × Option Int := Id.run do
  let clique := Q.all fun q => (g.node? q).isSome && Q.all fun s => (ownersB g q).contains s
  for i in List.range g.current_step.toNat do
    let l : Int := i
    if !(g.nodes.any fun n => n.id.id.step == l && Q.all n.owners.contains) then return (clique, some l)
  return (clique, none)

def showRes : Bool × Option Int → String
  | (c, none) => s!"clique={c} testigos=todos los pasos"
  | (c, some l) => s!"clique={c} sin testigo en el paso {l}"

def main (args : List String) : IO UInt32 := do
  let [path, s1, s2, s3, sj] := args | IO.println "uso: clausemix-probe f.cnf v1 v2 v3 j"; return 1
  let .ok φ := Dimacs.parse (← IO.FS.lines path).toList | IO.println "parse error"; return 1
  let vs := [s1.toNat!, s2.toNat!, s3.toNat!]
  let j := sj.toNat!
  let top : Int := clauseStep φ j 2
  let n := (top - 1).toNat
  IO.println s!"stepCount={stepCount φ}  L3 de la cláusula {j} = paso {top}"
  -- semantics
  let nv := φ.nVars
  let mut sols := 0
  for m in List.range (2 ^ nv) do
    let a : Assign := fun v => (m >>> v) % 2 == 1
    if vs.all a && φ.clauses.all (fun c => [c.l1, c.l2, c.l3].any fun l => a l.v == l.pos) then sols := sols + 1
  IO.println s!"soluciones de φ con v=1 en {vs}: {sols}"
  let l1 := pureSteps φ (n + 1) (pureInit φ)
  let l2 := pureAdvance φ l1
  -- the path nodes of `vᵢ = 1`
  let ids : List NodeId := vs.map fun v => selOfAssign φ (fun _ => true) (varStep v)
  let cands : NodeId → List PathNodeId := fun d => (allNodes l1).filter (·.id == d)
  IO.println s!"nodos de mapa de Q: {ids.map fun d => s!"{d.step}.{d.index}"}"
  IO.println s!"estados línea {top}: {l1.map fun kv => s!"{kv.1.step}.{kv.1.index}"}   línea {top+1}: {l2.map fun kv => s!"{kv.1.step}.{kv.1.index}"}"
  let [d1, d2, d3] := ids | return 1
  for q1 in cands d1 do
    for q2 in cands d2 do
      for q3 in cands d3 do
        let Q := [q1, q2, q3]
        let pairs := [(0, 1), (1, 2), (0, 2)].map fun (i, k) =>
          s!"{i}{k}:{ownsL l1 (Q.getD i q1) (Q.getD k q1)}/{ownsL l2 (Q.getD i q1) (Q.getD k q1)}"
        let (c1, w1) := lineTest l1 Q top
        IO.println s!"Q = {Q.map showP}  parejas (línea {top}/{top+1}) {pairs}"
        if !c1 then continue
        IO.println s!"  testigo que falla por entradas: {w1}"
        IO.println s!"  por entradas, línea {top}:   {showRes (lineTest l1 Q top)}"
        IO.println s!"  por entradas, línea {top+1}: {showRes (lineTest l2 Q (top + 1))}"
        for kv in l1 do
          IO.println s!"  estado {kv.1.step}.{kv.1.index} (línea {top}):   {showRes (stateTest (filterAll kv.2 []) Q)}"
        for kv in l2 do
          IO.println s!"  estado {kv.1.step}.{kv.1.index} (línea {top+1}): {showRes (stateTest (filterAll kv.2 []) Q)}"
  return 0
