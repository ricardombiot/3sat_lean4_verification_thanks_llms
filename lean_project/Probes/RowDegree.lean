import AbsSat.Cnf.Dimacs
import AbsSat.SatMachine.DiffTest
import AbsSat.GraphPath.Model.PureDriverImproves
import AbsSat.GraphPath.Model.ReaderExec
import AbsSat.GraphPath.Model.ReaderDescent
import AbsSat.GraphPath.Model.ReaderTop
import AbsSat.GraphPath.Model.ReaderBT

/-! # The in-degree of the row

Measures `ParentWitness.SingleParents` — *no node has two parents* — which
`Descent.commonOwner_of_singleParents` turns into the whole verdict of route C.
By `ParentWitness.parents_differ_below` two parents of a node agree on their map id and on
their own parent and differ only in the **grandparent**, so the in-degree of a node is
exactly the number of distinct two-step histories that converge on it.

Two numbers per run:

* **real** — the histogram of `n.parents.length` over every node of every state of every
  line. `SingleParents` holds iff the whole mass sits at 1 (step 0 has in-degree 0).
* **w2 vs w3** — the counterfactual. A row node of a window-`w` machine groups the previous
  line by its first `w-1` components, so grouping `g.line (k-1)` by `q.id` alone is what the
  in-degree *would* be with a window of two, and grouping by `(q.id, q.parent_id)` is what it
  is now. The gap between the two is what the third component bought.

Usage: `lake exe row-degree file <cnf>...`
       `lake exe row-degree random <cases> <minVars> <seed>...`
       `lake exe row-degree pm file|random ...`      -- ParentMeet / PairMeet, toda linea
       `lake exe row-degree traj[-sib] file|random ...`

El modo **`traj`** es el que mide la hipotesis que el lector consume de verdad
(`ReaderPairMeet.RunPairMeet`): recorre la trayectoria del lector desde cada estado de la linea
final —semilla, y un estado mas por cada pin— y en cada uno comprueba `PairMeet`, el in-degree, y
sobre todo **si al descenso le queda un owner comun para seguir bajando**. `traj-sib` mide ademas
los pines que el lector NO toma, que tambien son estados de `ReadFrom`.
-/

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.AggressiveReview (filterAllAgg)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphMap.CnfSel (mapSons)

namespace Probes.RowDegree

structure Acc where
  formulas : Nat := 0
  states   : Nat := 0
  nodes    : Nat := 0          -- nodes above step 0
  deg1     : Nat := 0          -- with exactly one parent
  degMore  : Nat := 0          -- with two or more
  degSum   : Nat := 0
  degMax   : Nat := 0
  moreLit  : Nat := 0          -- in-degree ≥2 inside the literal block
  moreCla  : Nat := 0          -- in-degree ≥2 at or above the clause block
  nodesLit : Nat := 0
  nodesCla : Nat := 0
  /-- counterfactual grouping of each line -/
  grp3     : Nat := 0          -- groups under the window of three (= row nodes now)
  grp2     : Nat := 0          -- groups under a window of two
  src      : Nat := 0          -- nodes of the line being grouped
  /-- the worst offender, for a pointer back into the corpus -/
  worstAt  : String := "-"
  /-- the direct `CommonOwner` test, over-approximated -/
  coNodes  : Nat := 0          -- nodes with ≥2 parents and at least one owner above
  coOk     : Nat := 0          -- ... where some single parent owns every owner above
  coFail   : Nat := 0
  coFailAt : String := "-"
  huntTried : Nat := 0
  huntChain : Nat := 0         -- el par SÍ es realizable ⇒ contraejemplo de CommonOwner
  huntNone  : Nat := 0         -- no hay cadena que pase por los dos
  huntOut   : Nat := 0         -- presupuesto agotado, indeciso
  huntNote  : String := "-"
  /-- la distancia de los pines al pick más bajo de una cadena -/
  pinTot    : Nat := 0
  pinD1     : Nat := 0         -- a 1 paso: gratis con ventana 2
  pinD2     : Nat := 0         -- a 2 pasos: gratis solo con ventana 3
  pinD3     : Nat := 0         -- a >=3 pasos: el residuo
  pinAbove  : Nat := 0         -- por encima o al mismo paso: gratis por node_id_of_pin
  pinMax    : Nat := 0
  loTot     : Nat := 0         -- pares (d, lo) con algún pin
  loClean   : Nat := 0         -- ... donde TODO pin está gratis (arriba, a 1 o a 2)
  loDirty   : Nat := 0
  /-- multiplicidad de la tabla: cuántos owners tiene un nodo en cada paso -/
  cellTot   : Nat := 0         -- pares (nodo, paso) con alguna entrada
  cell1     : Nat := 0         -- ... con exactamente una (decidido: parents_own_unique_owner)
  cellMore  : Nat := 0         -- ... con dos o más (el obstáculo)
  cellMax   : Nat := 0
  nodeClean : Nat := 0         -- nodos con TODAS sus celdas decididas
  nodeDirty : Nat := 0         -- ... donde queda algún pin a >=3
  /-- `Descent.ParentMeet`: ¿hay un padre que TODO owner del nodo posee? -/
  pmNodes   : Nat := 0         -- nodos con paso ≥1 y en rango
  pmOk      : Nat := 0
  pmFail    : Nat := 0
  pmMulti   : Nat := 0         -- ... de ellos, los que tienen ≥2 padres
  pmMultiOk : Nat := 0
  pmOwnMax  : Nat := 0         -- owners del nodo más cargado que pasó el test
  pmAllOk   : Nat := 0         -- la versión sin cota (ParentMeetAll)
  pmAllMultiOk : Nat := 0
  pmwTried  : Nat := 0         -- fallos de ParentMeet examinados
  pmwClique : Nat := 0         -- ... con los testigos compatibles entre sí (fallo REAL)
  pmwNo     : Nat := 0         -- ... con testigos incompatibles (fallo espurio)
  pmwNote   : String := "-"
  pmPairChk : Nat := 0         -- nodos donde se comprueba PairMeet (los que fallan ParentMeet)
  pmPairOk  : Nat := 0         -- ... donde PairMeet se cumple
  pmPairBad : Nat := 0         -- ... donde NO (contraejemplo de PairMeet)
  pmPairNote: String := "-"
  pmFailAt  : String := "-"
  deriving Repr

def bump (a : Acc) (d : Nat) (lit : Bool) : Acc :=
  { a with nodes := a.nodes + 1
         , deg1 := a.deg1 + (if d == 1 then 1 else 0)
         , degMore := a.degMore + (if d > 1 then 1 else 0)
         , degSum := a.degSum + d
         , degMax := max a.degMax d
         , nodesLit := a.nodesLit + (if lit then 1 else 0)
         , nodesCla := a.nodesCla + (if lit then 0 else 1)
         , moreLit := a.moreLit + (if d > 1 && lit then 1 else 0)
         , moreCla := a.moreCla + (if d > 1 && !lit then 1 else 0) }

/-- Count the distinct keys of a list, by a projection. -/
def distinctBy {α β : Type} [BEq β] (f : α → β) (l : List α) : Nat :=
  (l.foldl (fun acc x => if acc.contains (f x) then acc else f x :: acc) []).length

/-- **La obligación `extend_triple`, exacta.** Una cadena parcial que termina en `x` tiene sus picks
entre los owners de `x` por encima de él, y **se poseen mutuamente** (`SoundFrom.owned`). El primer
caso duro es el de dos picks: `u`, `w` owners de `x`, por encima, que se poseen entre sí. La
extensión tiene que ser un padre de `x`, y hace falta **uno solo** que posea a los dos.

`some false` es una violación genuina de la terna; `none` es que no hay caso que comprobar. -/
def tripleAt (g : GPathM) (x : PathNodeId) (n : PNodeM) (cap : Nat) : Option Bool :=
  if n.parents.length < 2 then none
  else Id.run do
    let above := (n.owners.filter (fun u => x.id.step < u.id.step)).take cap
    let mut seen := false
    let mut ok := true
    for u in above do
      for w in above do
        if u.id.step < w.id.step && (ownersOf g w).contains u && (ownersOf g u).contains w then
          seen := true
          if !(n.parents.any (fun c => (ownersOf g u).contains c && (ownersOf g w).contains c)) then
            ok := false
    return (if seen then some ok else none)

-- ============================================================
-- La caza: ¿el par que falla se realiza como picks de una cadena?
-- ============================================================

/-- Una cadena parcial sana desde `x` hacia arriba, forzada a pasar por `u` y `w`.

Los picks tienen que estar enlazados por links de padre (`sons`), poseerse **todos** entre sí,
y ser owners globales — es `SoundFrom` leído hacia arriba. Si esta búsqueda encuentra una, el par
que falló **sí** son picks de una cadena, y entonces esa cadena no extiende al paso de abajo: un
contraejemplo de `CommonOwner`. Si no encuentra ninguna, el par no era realizable y la relajación
era demasiado débil. -/
partial def chainThrough (g : GPathM) (u w : PathNodeId) (budget : Nat)
    (picks : List PathNodeId) (k : Int) : Nat × Option (List PathNodeId) :=
  if budget == 0 then (0, none)
  else if k ≥ g.current_step then (budget, some picks)
  else
    let prev := picks.headD u
    let cands := (sonsOf g prev).filter (fun c =>
      c.id.step == k
      && (if k == u.id.step then c == u else true)
      && (if k == w.id.step then c == w else true)
      && g.gowners.contains c
      && picks.all (fun p => (ownersOf g c).contains p && (ownersOf g p).contains c))
    cands.foldl (fun (st : Nat × Option (List PathNodeId)) c =>
      match st.2 with
      | some _ => st
      | none => chainThrough g u w (st.1 - 1) (c :: picks) (k + 1)) (budget, none)

/-- Devuelve el primer par `(u,w)` que falla la terna en `x`, si lo hay. -/
def failingPair (g : GPathM) (x : PathNodeId) (n : PNodeM) (cap : Nat) :
    Option (PathNodeId × PathNodeId) :=
  if n.parents.length < 2 then none
  else Id.run do
    let above := (n.owners.filter (fun u => x.id.step < u.id.step)).take cap
    for u in above do
      for w in above do
        if u.id.step < w.id.step && (ownersOf g w).contains u && (ownersOf g u).contains w then
          if !(n.parents.any (fun c => (ownersOf g u).contains c && (ownersOf g w).contains c)) then
            return some (u, w)
    return none

/-- **`Descent.ParentMeet`, nodo a nodo.** ¿Existe un padre `c` del nodo tal que **todo** owner del
nodo —que sea a su vez nodo del estado y esté en rango— lleve a `c` en su propia tabla?

Es exactamente lo que `Descent.commonOwner_of_parentMeet` consume, y `SingleParents` es el caso
degenerado en que solo hay un padre que probar. Ojo: con un solo padre el test **no** es trivial —
ese padre tiene que estar en la tabla de todos los owners, que es lo que
`parentMeet_of_singleParents` deduce de la criba. -/
def parentMeetAt (g : GPathM) (n : PNodeM) : Bool :=
  let ys := n.owners.filter
    (fun y => decide (n.id.id.step ≤ y.id.step ∧ y.id.step < g.current_step))
  let tabs := ys.filterMap (fun y => (g.node? y).map (·.owners))
  n.parents.any (fun c => tabs.all (fun os => os.contains c))

/-- `Descent.ParentMeetAll`: lo mismo **sin** la cota, o sea incluyendo los owners por debajo del
nodo. `singleParent_of_parentMeetAll` demuestra que eso obliga a padre único; se mide para ver el
contraste, no porque haga falta. -/
def parentMeetAllAt (g : GPathM) (n : PNodeM) : Bool :=
  let ys := n.owners.filter (fun y => decide (0 ≤ y.id.step ∧ y.id.step < g.current_step))
  let tabs := ys.filterMap (fun y => (g.node? y).map (·.owners))
  n.parents.any (fun c => tabs.all (fun os => os.contains c))

/-- Dos nodos que se poseen mutuamente: condición necesaria para ser picks de una misma cadena. -/
def mutuallyOwn (g : GPathM) (u v : PathNodeId) : Bool :=
  match g.node? u, g.node? v with
  | some mu, some mv => mu.owners.contains v && mv.owners.contains u
  | _, _ => false

/-- Para un nodo que falla `ParentMeet`, un testigo por cada padre: el owner de arriba que **no**
lleva a ese padre. Si falla, hay testigo para todos. -/
def parentMeetWitnesses (g : GPathM) (n : PNodeM) : Option (List PathNodeId) :=
  let ys := n.owners.filter
    (fun y => decide (n.id.id.step ≤ y.id.step ∧ y.id.step < g.current_step))
  let pick (c : PathNodeId) : Option PathNodeId :=
    ys.find? (fun y => match g.node? y with
                       | none => false
                       | some m => !m.owners.contains c)
  let ws := n.parents.filterMap pick
  if ws.length == n.parents.length then some ws else none

/-- ¿Son los testigos compatibles entre sí? Si no lo son, no pueden ser picks de la misma cadena
parcial, y el fallo de `ParentMeet` **no** contradice `CommonOwner`. -/
def witnessesClique (g : GPathM) (ws : List PathNodeId) : Bool :=
  ws.all (fun u => ws.all (fun v => u == v || mutuallyOwn g u v))

/-- **`Descent.PairMeet` en un nodo, exacto.** ¿Todo par de owners por encima del nodo que se
poseen mutuamente comparte un padre del nodo?

Solo hace falta comprobarlo donde `ParentMeet` falla: si algún padre está en la tabla de todos los
owners de arriba, todo par lo comparte y `PairMeet` es automático. -/
def pairMeetAt (g : GPathM) (n : PNodeM) : Bool :=
  let ys := n.owners.filter
    (fun y => decide (n.id.id.step ≤ y.id.step ∧ y.id.step < g.current_step))
  let tab := fun (y : PathNodeId) =>
    match g.node? y with | some m => m.owners | none => ([] : List PathNodeId)
  let shares := fun (u v : PathNodeId) =>
    n.parents.any (fun c => (tab u).contains c && (tab v).contains c)
  ys.all (fun u => ys.all (fun v => shares u v || !mutuallyOwn g u v))

/-- Solo el in-degree y `ParentMeet`, sin las sondas caras. -/
def scanStatePM (lb : Int) (label : String) (g : GPathM) (a : Acc) : Acc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for n in g.nodes do
    if n.id.id.step > 0 then
      a := bump a n.parents.length (n.id.id.step < lb)
      if n.id.id.step < g.current_step then
        let ok := parentMeetAt g n
        let okAll := parentMeetAllAt g n
        let multi := n.parents.length > 1
        a := { a with pmNodes := a.pmNodes + 1
                    , pmOk := a.pmOk + (if ok then 1 else 0)
                    , pmFail := a.pmFail + (if ok then 0 else 1)
                    , pmMulti := a.pmMulti + (if multi then 1 else 0)
                    , pmMultiOk := a.pmMultiOk + (if multi && ok then 1 else 0)
                    , pmAllOk := a.pmAllOk + (if okAll then 1 else 0)
                    , pmAllMultiOk := a.pmAllMultiOk + (if multi && okAll then 1 else 0)
                    , pmOwnMax := if ok then max a.pmOwnMax n.owners.length else a.pmOwnMax }
        if !ok then
          a := { a with pmFailAt :=
            s!"{label} paso {n.id.id.step}, {n.parents.length} padres, {n.owners.length} owners" }
          let pmp := pairMeetAt g n
          a := { a with pmPairChk := a.pmPairChk + 1
                      , pmPairOk := a.pmPairOk + (if pmp then 1 else 0)
                      , pmPairBad := a.pmPairBad + (if pmp then 0 else 1) }
          if !pmp then
            a := { a with pmPairNote :=
              s!"{label} paso {n.id.id.step}, {n.parents.length} padres, {n.owners.length} owners" }
          match parentMeetWitnesses g n with
          | none => pure ()
          | some ws =>
            let cl := witnessesClique g ws
            a := { a with pmwTried := a.pmwTried + 1
                        , pmwClique := a.pmwClique + (if cl then 1 else 0)
                        , pmwNo := a.pmwNo + (if cl then 0 else 1)
                        , pmwNote := s!"{label} paso {n.id.id.step} testigos {ws.length} {if cl then "COMPATIBLES" else "incompatibles"}" }
  return a

def scanState (lb : Int) (label : String) (g : GPathM) (a : Acc) : Acc := Id.run do
  let mut a := { a with states := a.states + 1 }
  -- (1) the real in-degree, node by node
  for n in g.nodes do
    if n.id.id.step > 0 then
      let d := n.parents.length
      if d > a.degMax then
        a := { a with worstAt := s!"{label} step {n.id.id.step} deg {d}" }
      a := bump a d (n.id.id.step < lb)
      match tripleAt g n.id n 40 with
      | none => pure ()
      | some true => a := { a with coNodes := a.coNodes + 1, coOk := a.coOk + 1 }
      | some false =>
        a := { a with coNodes := a.coNodes + 1, coFail := a.coFail + 1
                    , coFailAt := s!"{label} step {n.id.id.step}" }
        match failingPair g n.id n 40 with
        | none => pure ()
        | some (u, w) =>
          a := { a with huntTried := a.huntTried + 1 }
          let (left, res) := chainThrough g u w 200000 [n.id] (n.id.id.step + 1)
          match res with
          | some _ =>
            a := { a with huntChain := a.huntChain + 1
                        , huntNote := s!"{label} x@{n.id.id.step} u@{u.id.step} w@{w.id.step} CADENA" }
          | none =>
            if left == 0 then
              a := { a with huntOut := a.huntOut + 1
                          , huntNote := s!"{label} x@{n.id.id.step} presupuesto agotado" }
            else
              a := { a with huntNone := a.huntNone + 1
                          , huntNote := s!"{label} x@{n.id.id.step} u@{u.id.step} w@{w.id.step} sin cadena" }
  -- (1bis) la multiplicidad de la tabla, celda por celda
  for n in g.nodes do
    if n.id.id.step > 0 then
      let mut clean := true
      let mut j : Int := 0
      while j < g.current_step do
        let cnt := (n.owners.filter (fun q => q.id.step == j)).length
        if cnt > 0 then
          a := { a with cellTot := a.cellTot + 1
                      , cell1 := a.cell1 + (if cnt == 1 then 1 else 0)
                      , cellMore := a.cellMore + (if cnt > 1 then 1 else 0)
                      , cellMax := max a.cellMax cnt }
          if cnt > 1 then clean := false
        j := j + 1
      a := { a with nodeClean := a.nodeClean + (if clean then 1 else 0)
                  , nodeDirty := a.nodeDirty + (if clean then 0 else 1) }
  -- (2) the counterfactual, line by line
  let mut k : Int := 0
  while k < g.current_step - 1 do
    let ids := (g.line k).map (·.id)
    if !ids.isEmpty then
      a := { a with src := a.src + ids.length
                  , grp2 := a.grp2 + distinctBy (fun q => q.id) ids
                  , grp3 := a.grp3 + distinctBy (fun q => (q.id, q.parent_id)) ids }
    k := k + 1
  return a

/-- **A qué distancia del pick más bajo caen los pines.** Para cada nodo de mapa `d` que el mapa
visita, `reqOfCnf φ d` son los pines que el envío a `d` aplica; el pick más bajo de una cadena
parcial puede estar en cualquier paso `lo` del estado. Se cuenta, para cada `(d, lo)` posible, la
distancia `lo - req.step` de cada pin: `1` y `2` son gratis (`pins_below_free`), `≥3` es el
residuo, y `≤0` es gratis por `node_id_of_pin`. -/
def scanPins (φ : Cnf) (a : Acc) : Acc := Id.run do
  let mut a := a
  let cs := stepCount φ
  let mut k : Int := 0
  while k < cs do
    for d in mapNodes φ k do
      -- ¿a este `lo` le queda algún pin a distancia >= 3?
      let mut lo2 : Int := 1
      while lo2 ≤ d.step do
        let pins := reqOfCnf φ d
        if !pins.isEmpty then
          let far := pins.any (fun req => lo2 - req.step ≥ 3)
          a := { a with loTot := a.loTot + 1
                      , loClean := a.loClean + (if far then 0 else 1)
                      , loDirty := a.loDirty + (if far then 1 else 0) }
        lo2 := lo2 + 1
      for req in reqOfCnf φ d do
        -- el envío a `d` deja el estado con `current_step = d.step + 1`, así que el pick más
        -- bajo de una cadena parcial vive en `1 .. d.step`
        let mut lo : Int := 1
        while lo ≤ d.step do
          let dist := lo - req.step
          a := { a with pinTot := a.pinTot + 1
                      , pinAbove := a.pinAbove + (if dist ≤ 0 then 1 else 0)
                      , pinD1 := a.pinD1 + (if dist == 1 then 1 else 0)
                      , pinD2 := a.pinD2 + (if dist == 2 then 1 else 0)
                      , pinD3 := a.pinD3 + (if dist ≥ 3 then 1 else 0)
                      , pinMax := max a.pinMax (if dist ≤ 0 then 0 else dist.toNat) }
          lo := lo + 1
    k := k + 1
  return a

/-- Every line of the run, not just the last. -/
def runFormula (φ : Cnf) (a : Acc) : Acc := Id.run do
  let mut a := scanPins φ { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for i in [0:steps] do
    line := pureAdvanceW φ line
    for kv in line do
      a := scanState (litBlock φ) s!"line {i+1} key ⟨{kv.1.step},{kv.1.index}⟩" kv.2 a
  return a

def report (name : String) (a : Acc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, states {a.states}, nodes above step 0: {a.nodes}"
  IO.println s!"   in-degree 1  : {a.deg1}  ({pct a.deg1 a.nodes})"
  IO.println s!"   in-degree ≥2 : {a.degMore}  ({pct a.degMore a.nodes})   max {a.degMax}"
  if a.nodes > 0 then
    let c := a.degSum * 100 / a.nodes
    IO.println s!"   mean         : {c / 100}.{if c % 100 < 10 then "0" else ""}{c % 100}"
    IO.println s!"   ≥2 literales: {a.moreLit}/{a.nodesLit} ({pct a.moreLit a.nodesLit})   ≥2 clausulas: {a.moreCla}/{a.nodesCla} ({pct a.moreCla a.nodesCla})"
  IO.println s!"   SingleParents: {if a.degMore == 0 then "HOLDS" else "fails"}"
  IO.println s!"   grouping of the previous line: {a.src} ids → {a.grp2} groups (w=2), {a.grp3} groups (w=3)"
  if a.degMore > 0 then IO.println s!"   worst: {a.worstAt}"
  IO.println s!"   extend_triple (nodos con ≥2 padres y algún par de picks): {a.coNodes}"
  IO.println s!"     un padre sirve para toda pareja : {a.coOk}  ({pct a.coOk a.coNodes})"
  IO.println s!"     alguna pareja sin padre común  : {a.coFail}"
  if a.coFail > 0 then IO.println s!"     primero: {a.coFailAt}"
  if a.huntTried > 0 then
    IO.println s!"   caza sobre los fallos ({a.huntTried}):"
    IO.println s!"     el par ES picks de una cadena (contraejemplo) : {a.huntChain}"
    IO.println s!"     no hay cadena por los dos (relajacion debil)  : {a.huntNone}"
    IO.println s!"     indeciso (presupuesto agotado)                : {a.huntOut}"
    IO.println s!"     ultimo: {a.huntNote}"
  if a.cellTot > 0 then
    IO.println s!"   multiplicidad de las tablas ({a.cellTot} celdas (nodo, paso) no vacias):"
    IO.println s!"     un solo owner (decidido)  : {a.cell1}  ({pct a.cell1 a.cellTot})"
    IO.println s!"     dos o mas (el obstaculo)  : {a.cellMore}  ({pct a.cellMore a.cellTot})   max {a.cellMax}"
    IO.println s!"     nodos con TODAS decididas : {a.nodeClean}/{a.nodeClean + a.nodeDirty}  ({pct a.nodeClean (a.nodeClean + a.nodeDirty)})"
  if a.pinTot > 0 then
    IO.println s!"   distancia de los pines al pick mas bajo ({a.pinTot} pares (pin, lo)):"
    IO.println s!"     por encima o igual (gratis, node_id_of_pin) : {a.pinAbove}  ({pct a.pinAbove a.pinTot})"
    IO.println s!"     a 1 paso  (gratis ya con ventana 2)        : {a.pinD1}  ({pct a.pinD1 a.pinTot})"
    IO.println s!"     a 2 pasos (gratis SOLO con ventana 3)      : {a.pinD2}  ({pct a.pinD2 a.pinTot})"
    IO.println s!"     a >=3 pasos (EL RESIDUO)                   : {a.pinD3}  ({pct a.pinD3 a.pinTot})   max {a.pinMax}"
    IO.println s!"   y por (d, lo): de {a.loTot} posiciones del pick mas bajo,"
    IO.println s!"     TODOS los pines gratis (arriba, a 1 o a 2)  : {a.loClean}  ({pct a.loClean a.loTot})"
    IO.println s!"     queda algun pin a >=3 pasos                 : {a.loDirty}  ({pct a.loDirty a.loTot})"
  IO.println s!"   ({ms} ms)"

def runFormulaPM (φ : Cnf) (a : Acc) : Acc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for i in [0:steps] do
    line := pureAdvanceW φ line
    for kv in line do
      a := scanStatePM (litBlock φ) s!"linea {i+1} clave ⟨{kv.1.step},{kv.1.index}⟩" kv.2 a
  return a

def reportPM (name : String) (a : Acc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, nodos por encima del paso 0: {a.nodes}"
  IO.println s!"   in-degree 1  : {a.deg1}  ({pct a.deg1 a.nodes})"
  IO.println s!"   in-degree ≥2 : {a.degMore}  ({pct a.degMore a.nodes})   max {a.degMax}"
  IO.println s!"   ParentMeet ({a.pmNodes} nodos en rango):"
  IO.println s!"     algun padre lo poseen TODOS : {a.pmOk}  ({pct a.pmOk a.pmNodes})"
  IO.println s!"     ningun padre sirve (FALLO)  : {a.pmFail}"
  IO.println s!"     entre los de ≥2 padres      : {a.pmMultiOk}/{a.pmMulti}  ({pct a.pmMultiOk a.pmMulti})"
  IO.println s!"     tabla mas grande que pasa   : {a.pmOwnMax} owners"
  IO.println s!"   ParentMeet: {if a.pmFail == 0 then "SE CUMPLE" else "FALLA"}"
  IO.println s!"   ParentMeetAll (sin la cota, el colapso demostrado):"
  IO.println s!"     lo cumplen                  : {a.pmAllOk}  ({pct a.pmAllOk a.pmNodes})"
  IO.println s!"     entre los de ≥2 padres      : {a.pmAllMultiOk}/{a.pmMulti}"
  if a.pmFail > 0 then IO.println s!"     primero: {a.pmFailAt}"
  if a.pmwTried > 0 then
    IO.println s!"   los fallos, examinados ({a.pmwTried}):"
    IO.println s!"     testigos compatibles entre si (fallo REAL) : {a.pmwClique}"
    IO.println s!"     testigos incompatibles (fallo espurio)     : {a.pmwNo}"
    IO.println s!"     ultimo: {a.pmwNote}"
  if a.pmPairChk > 0 then
    IO.println s!"   PairMeet, exacto, en los {a.pmPairChk} nodos donde ParentMeet falla:"
    IO.println s!"     se cumple            : {a.pmPairOk}  ({pct a.pmPairOk a.pmPairChk})"
    IO.println s!"     CONTRAEJEMPLO        : {a.pmPairBad}"
    if a.pmPairBad > 0 then IO.println s!"     primero: {a.pmPairNote}"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- La trayectoria del lector: `ReaderPairMeet.RunPairMeet`
-- ============================================================

/-! `ReaderPairMeet.answer_ne_unknown_pm` pide `PairMeet` **en todo estado que el lector alcanza**,
no solo en el final. Y lo que el descenso consume de esos estados es una cosa muy concreta, que es
la que esta sonda mide de frente: **que quede un owner común un paso más abajo**, para poder seguir
bajando y descubrir el camino. `TwoParents` no hace falta medirlo por la trayectoria
(`ReaderPairMeet.twoParents_of_pruned` lo baja solo), pero se mide igual porque si algún estado
tiene in-degree 3 el argumento de Helly con número 2 se cae. -/

structure TAcc where
  formulas : Nat := 0
  finals   : Nat := 0          -- estados de la línea final
  seeds    : Nat := 0          -- ... que un review deja válidos: las semillas del lector
  visited  : Nat := 0          -- estados de la trayectoria medidos
  sibling  : Nat := 0          -- ... de ellos, pines que el lector NO tomó (más de `ReadFrom`)
  pins     : Nat := 0
  finished : Nat := 0          -- trayectorias en que el lector llega al final
  stuck    : Nat := 0          -- ... en que se atasca: ningún pin del paso deja válido
  stuckAt  : String := "-"
  /-- `TwoParents` -/
  degMax   : Nat := 0
  tpFail   : Nat := 0          -- estados con algún nodo de ≥3 padres
  tpFailAt : String := "-"
  /-- `PairMeet`, exacto, donde `ParentMeet` no lo hace automático -/
  pmChk    : Nat := 0
  pmOk     : Nat := 0
  pmBad    : Nat := 0
  pmBadAt  : String := "-"
  /-- el descenso: ¿queda owner común para seguir bajando? -/
  dscTried : Nat := 0          -- estados en los que se intenta el descenso
  dscFull  : Nat := 0          -- ... que llegan al paso 0: hay camino
  dscStall : Nat := 0          -- ... que se quedan sin owner común
  dscNoTop : Nat := 0          -- ... sin ancla arriba (no debería pasar en estado válido)
  dscOut   : Nat := 0          -- ... indecisos, presupuesto agotado
  dscStallAt : String := "-"
  coSteps  : Nat := 0          -- pasos de descenso intentados
  coOkStep : Nat := 0          -- ... con al menos un owner común
  coCands  : Nat := 0          -- suma de owners comunes disponibles por paso
  coMax    : Nat := 0
  /-- `Descent.DecidedAbove`: ¿tiene la tabla de un nodo una sola entrada en cada paso POR ENCIMA? -/
  decCells : Nat := 0          -- celdas (nodo, paso≥suyo) no vacias
  decMore  : Nat := 0          -- ... con dos o mas entradas
  decMax   : Nat := 0
  decOk    : Nat := 0          -- estados donde DecidedAbove se cumple entero
  decBad   : Nat := 0
  decBadAt : String := "-"
  /-- `Descent.MapPinnedFrom`: cuantos pasos desde arriba tienen el id de mapa ya fijado -/
  zoneSum  : Nat := 0          -- suma de la profundidad de la zona pinchada
  zoneMax  : Nat := 0
  zoneFull : Nat := 0          -- estados con TODA la corrida pinchada (MapPinnedFrom _ 1)
  stepsSum : Nat := 0          -- suma de current_step, para el porcentaje
  deriving Repr

/-- **Los owners comunes que el descenso puede usar.** Un paso más abajo del pick más bajo, y
poseído por **todos** los picks ya hechos — que es lo que `Descent.extend_of_common_owner` consume, y
lo que `PairMeet` promete par a par. Por `owners_below_iff_parents` un owner un paso por debajo es
un padre, así que se buscan entre los padres. -/
def commonOwners (g : GPathM) (picks : List PathNodeId) : List PathNodeId :=
  match picks with
  | [] => []
  | x :: _ =>
    match g.node? x with
    | none => []
    | some n => n.parents.filter (fun c =>
        g.gowners.contains c && picks.all (fun y => mutuallyOwn g c y))

/-- El ancla de arriba: un owner global del paso más alto que es nodo y se posee a sí mismo. Es lo
que `NoDeadEnd.topAnchor_of` da gratis en un estado válido. -/
def topAnchors (g : GPathM) : List PathNodeId :=
  (g.gowners.filter (fun q => q.id.step == g.current_step - 1)).filter (fun q =>
    match g.node? q with | some m => m.owners.contains q | none => false)

structure DAcc where
  budget : Nat := 0
  steps  : Nat := 0
  okStep : Nat := 0
  cands  : Nat := 0
  mx     : Nat := 0
  lowest : Int := 0
  done   : Bool := false
  deriving Repr

/-- **El descenso, con retroceso acotado.** `picks` cubre los pasos `k+1 .. top`; toca llenar `k`.
Se para en éxito al pasar del 0. Si se queda sin candidatos en algún paso y ningún retroceso lo
arregla, ese estado es un contraejemplo de `NoDeadEnd` — y por tanto de `CommonOwner`. -/
partial def descendFrom (g : GPathM) (picks : List PathNodeId) (k : Int) (d : DAcc) : DAcc :=
  if d.done || d.budget == 0 then d
  else if k < 0 then { d with done := true, lowest := -1 }
  else
    let cs := commonOwners g picks
    let d := { d with budget := d.budget - 1, steps := d.steps + 1
                    , okStep := d.okStep + (if cs.isEmpty then 0 else 1)
                    , cands := d.cands + cs.length
                    , mx := max d.mx cs.length
                    , lowest := min d.lowest k }
    cs.foldl (fun acc c => if acc.done then acc else descendFrom g (c :: picks) (k - 1) acc) d

/-- `Descent.DecidedAbove`, nodo a nodo: celdas (paso ≥ el del nodo) y cuantas tienen ≥2 entradas. -/
def decidedAboveStats (g : GPathM) (n : PNodeM) : Nat × Nat × Nat := Id.run do
  let ws := n.owners.filter
    (fun w => decide (n.id.id.step ≤ w.id.step ∧ w.id.step < g.current_step))
  let steps := ws.foldl (fun acc w => if acc.contains w.id.step then acc else w.id.step :: acc) []
  let mut cells := 0
  let mut more := 0
  let mut mx := 0
  for j in steps do
    let c := distinctBy (fun (w : PathNodeId) => w) (ws.filter (fun w => w.id.step == j))
    cells := cells + 1
    if c > 1 then more := more + 1
    mx := max mx c
  return (cells, more, mx)

/-- **La zona pinchada**, medida: cuantos pasos consecutivos desde arriba tienen todos sus owners
globales con el mismo id de mapa. Es `Descent.MapPinnedFrom g (current_step - zona)`, y es la
hipotesis que `Descent.extend_below_pinned` consume. -/
def pinnedZone (g : GPathM) : Nat := Id.run do
  let mut depth := 0
  let mut k := g.current_step - 1
  while k ≥ 0 do
    let ids := (g.gowners.filter (fun q => q.id.step == k)).map (fun q => q.id)
    let distinct := distinctBy (fun (d : NodeId) => d) ids
    if distinct ≤ 1 then
      depth := depth + 1
      k := k - 1
    else
      k := -1
  return depth

/-- Un estado de la trayectoria, medido: `TwoParents`, `PairMeet` y el descenso. -/
def measureTraj (label : String) (g : GPathM) (isSib : Bool) (a : TAcc) : TAcc := Id.run do
  let mut a := { a with visited := a.visited + 1
                      , sibling := a.sibling + (if isSib then 1 else 0) }
  let mut mx := 0
  let mut dbad := 0
  for n in g.nodes do
    if n.id.id.step > 0 then
      mx := max mx n.parents.length
      let (dc, dm, dx) := decidedAboveStats g n
      dbad := dbad + dm
      a := { a with decCells := a.decCells + dc, decMore := a.decMore + dm
                  , decMax := max a.decMax dx }
      if n.id.id.step < g.current_step && n.parents.length > 1 && !parentMeetAt g n then
        let ok := pairMeetAt g n
        a := { a with pmChk := a.pmChk + 1
                    , pmOk := a.pmOk + (if ok then 1 else 0)
                    , pmBad := a.pmBad + (if ok then 0 else 1) }
        if !ok then
          a := { a with pmBadAt :=
            s!"{label} paso {n.id.id.step}, {n.parents.length} padres, {n.owners.length} owners" }
  a := { a with degMax := max a.degMax mx
              , decOk := a.decOk + (if dbad == 0 then 1 else 0)
              , decBad := a.decBad + (if dbad == 0 then 0 else 1) }
  if dbad > 0 then
    a := { a with decBadAt := s!"{label}: {dbad} celdas con ≥2 entradas por encima" }
  a := { a with degMax := max a.degMax mx }
  if mx > 2 then
    a := { a with tpFail := a.tpFail + 1, tpFailAt := s!"{label} in-degree {mx}" }
  let zone := pinnedZone g
  a := { a with zoneSum := a.zoneSum + zone
              , zoneMax := max a.zoneMax zone
              , stepsSum := a.stepsSum + g.current_step.toNat
              , zoneFull := a.zoneFull + (if (zone : Int) ≥ g.current_step then 1 else 0) }
  let top := g.current_step - 1
  a := { a with dscTried := a.dscTried + 1 }
  match topAnchors g with
  | [] => a := { a with dscNoTop := a.dscNoTop + 1 }
  | q :: _ =>
    let d := descendFrom g [q] (top - 1) { budget := 200000, lowest := top }
    a := { a with coSteps := a.coSteps + d.steps
                , coOkStep := a.coOkStep + d.okStep
                , coCands := a.coCands + d.cands
                , coMax := max a.coMax d.mx }
    if d.done then a := { a with dscFull := a.dscFull + 1 }
    else if d.budget == 0 then a := { a with dscOut := a.dscOut + 1 }
    else
      a := { a with dscStall := a.dscStall + 1
                  , dscStallAt := s!"{label}: bajó hasta el paso {d.lowest} de {top}" }
  return a

/-- Recorre la trayectoria del lector: el mismo paso que `ReaderExec.readLoop` da, y —si `sibs`— los
demás pines válidos de ese paso, que también son estados de `ReadFrom`. -/
partial def walkReader (topDown sibs : Bool) (label : String) (g : GPathM) (fuel : Nat) (a : TAcc) :
    TAcc := Id.run do
  let mut a := measureTraj label g false a
  match (if topDown then ReaderTop.lastChoice g else ReaderExec.firstChoice g) with
  | none => return { a with finished := a.finished + 1 }
  | some k =>
    let mut chosen : Option GPathM := none
    for q in ownersAt g.gowners k do
      let h := filterAllAgg g [q.id]
      if isValid h then
        match chosen with
        | none => chosen := some h
        | some _ => if sibs then a := measureTraj s!"{label}|hermano@{k}" h true a
    match chosen with
    | none => return { a with stuck := a.stuck + 1
                            , stuckAt := s!"{label}: ningún pin válido en el paso {k}" }
    | some h =>
      if fuel == 0 then return a
      return walkReader topDown sibs s!"{label}+pin@{k}" h (fuel - 1) { a with pins := a.pins + 1 }

def runFormulaTraj (topDown sibs : Bool) (φ : Cnf) (a : TAcc) : TAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    a := { a with finals := a.finals + 1 }
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with seeds := a.seeds + 1 }
      a := walkReader topDown sibs s!"⟨{kv.1.step},{kv.1.index}⟩" g (measure g) a
  return a

def reportTraj (name : String) (a : TAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados finales {a.finals}, semillas validas {a.seeds}"
  IO.println s!"   trayectoria: {a.visited} estados medidos ({a.sibling} hermanos), {a.pins} pines"
  IO.println s!"     el lector termina : {a.finished}"
  IO.println s!"     el lector SE ATASCA: {a.stuck}"
  if a.stuck > 0 then IO.println s!"       primero: {a.stuckAt}"
  IO.println s!"   TwoParents: in-degree maximo {a.degMax}, estados con ≥3 padres: {a.tpFail}"
  if a.tpFail > 0 then IO.println s!"     primero: {a.tpFailAt}"
  IO.println s!"   PairMeet, exacto, en los {a.pmChk} nodos donde ParentMeet no lo hace automatico:"
  IO.println s!"     se cumple     : {a.pmOk}  ({pct a.pmOk a.pmChk})"
  IO.println s!"     CONTRAEJEMPLO : {a.pmBad}"
  if a.pmBad > 0 then IO.println s!"     primero: {a.pmBadAt}"
  IO.println s!"   RunPairMeet: {if a.pmBad == 0 then "SE CUMPLE en la trayectoria medida" else "FALLA"}"
  IO.println s!"   DecidedAbove ({a.decCells} celdas (nodo, paso≥suyo) no vacias):"
  IO.println s!"     una sola entrada : {a.decCells - a.decMore}  ({pct (a.decCells - a.decMore) a.decCells})"
  IO.println s!"     dos o mas        : {a.decMore}   max {a.decMax}"
  IO.println s!"     estados donde SE CUMPLE entero: {a.decOk}/{a.decOk + a.decBad}"
  if a.decBad > 0 then IO.println s!"     primero: {a.decBadAt}"
  IO.println s!"   zona pinchada (MapPinnedFrom: pasos desde arriba con id de mapa fijado):"
  IO.println s!"     profundidad media : {if a.visited == 0 then 0 else a.zoneSum / a.visited} de {if a.visited == 0 then 0 else a.stepsSum / a.visited} pasos   ({pct a.zoneSum a.stepsSum})"
  IO.println s!"     maxima            : {a.zoneMax}"
  IO.println s!"     estados con TODA la corrida pinchada : {a.zoneFull}/{a.visited}"
  IO.println s!"   el descenso (owners comunes para seguir bajando), {a.dscTried} estados:"
  IO.println s!"     llega al paso 0 (hay camino) : {a.dscFull}  ({pct a.dscFull a.dscTried})"
  IO.println s!"     SE QUEDA SIN OWNER COMUN     : {a.dscStall}"
  IO.println s!"     indeciso (presupuesto)       : {a.dscOut}"
  IO.println s!"     sin ancla arriba             : {a.dscNoTop}"
  if a.dscStall > 0 then IO.println s!"     primero: {a.dscStallAt}"
  if a.coSteps > 0 then
    IO.println s!"   por paso de descenso ({a.coSteps} intentos):"
    IO.println s!"     con owner comun : {a.coOkStep}  ({pct a.coOkStep a.coSteps})   max {a.coMax} candidatos"
    let m := a.coCands * 100 / a.coSteps
    IO.println s!"     media de owners comunes por paso: {m / 100}.{if m % 100 < 10 then "0" else ""}{m % 100}"
  IO.println s!"   ({ms} ms)"


-- ============================================================
-- ¿Retrocede alguna vez el lector?
-- ============================================================

/-! `ReaderBT.readerVerdictBT_iff` demuestra que el lector con retroceso decide, sin hipotesis. Lo
que queda abierto es el COSTE: cuantas veces retrocede. Esta sonda lo mide de frente comparando los
tres lectores sobre cada estado de la linea final:

* `readAgg`    — sin retroceso, primer paso con eleccion (`ReaderExec`)
* `readAggTop` — sin retroceso, ultimo paso con eleccion (`ReaderTop`)
* `readAggBT`  — con retroceso (`ReaderBT`), demostrado completo

Un estado donde `readAggBT` acierta y `readAgg` no es un estado donde el retroceso HACE FALTA. -/

structure BAcc where
  formulas : Nat := 0
  finals   : Nat := 0
  seeds    : Nat := 0          -- estados validos tras el review del lector
  okW      : Nat := 0          -- los resuelve el lector sin retroceso (abajo arriba)
  okTop    : Nat := 0          -- ... el de arriba abajo
  okBT     : Nat := 0          -- ... el de retroceso
  needW    : Nat := 0          -- BT acierta y W no: el retroceso HACE FALTA
  needTop  : Nat := 0          -- BT acierta y Top no
  needAt   : String := "-"
  deriving Repr

def runFormulaBT (φ : Cnf) (a : BAcc) : BAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    a := { a with finals := a.finals + 1 }
    let g := filterAllAgg kv.2 []
    if isValid g then
      let w := (ReaderExec.readAgg g).isSome
      let t := (ReaderTop.readAggTop g).isSome
      let b := (ReaderBT.readAggBT g).isSome
      a := { a with seeds := a.seeds + 1
                  , okW := a.okW + (if w then 1 else 0)
                  , okTop := a.okTop + (if t then 1 else 0)
                  , okBT := a.okBT + (if b then 1 else 0)
                  , needW := a.needW + (if b && !w then 1 else 0)
                  , needTop := a.needTop + (if b && !t then 1 else 0) }
      if b && !w then
        a := { a with needAt := s!"clave ⟨{kv.1.step},{kv.1.index}⟩" }
  return a

def reportBT (name : String) (a : BAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados finales {a.finals}, semillas validas {a.seeds}"
  IO.println s!"   resuelven la semilla:"
  IO.println s!"     sin retroceso, abajo arriba (ReaderExec) : {a.okW}"
  IO.println s!"     sin retroceso, arriba abajo (ReaderTop)  : {a.okTop}"
  IO.println s!"     con retroceso (ReaderBT, demostrado)     : {a.okBT}"
  IO.println s!"   EL RETROCESO HACE FALTA en: {a.needW} estados (vs abajo arriba), {a.needTop} (vs arriba abajo)"
  if a.needW > 0 then IO.println s!"     primero: {a.needAt}"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- `doJoin`, instrumentado, y la transitividad remedida
-- ============================================================

/-! `insertPure` une dos estados que llegan al mismo nodo de mapa **sin revisar**: el review llega en
el envío siguiente (`upFilteringWeak` = débiles → duros → `reviewAgg` → `up`). Esta sonda mira cada
join de la corrida y responde a dos preguntas:

1. ¿cuántos joins fusionan un nodo que está en los dos lados **con listas de padres distintas**? Ese
   es el único caso que puede romper `AllParentsOwn` (`Descent.gained_of_parent` demuestra que el
   `up` la conserva);
2. ¿la restablece el review que viene después?

Y remide la transitividad de la posesión, que la medida vieja (52.720/380.746) tomó **antes** de que
el identificador llevara tres componentes. -/

structure JAcc where
  formulas  : Nat := 0
  sends     : Nat := 0
  joins     : Nat := 0         -- envios que caen sobre una clave ya presente
  merged    : Nat := 0         -- nodos presentes en los dos lados
  diffPar   : Nat := 0         -- ... con listas de padres DISTINTAS (el unico peligro)
  diffParAt : String := "-"
  /-- `AllParentsOwn`, contando fallos (nodo, owner, padre) -/
  apoA      : Nat := 0         -- fallos en el lado ya presente
  apoB      : Nat := 0         -- fallos en el lado que llega
  apoJ      : Nat := 0         -- fallos en la union, antes de revisar
  apoR      : Nat := 0         -- fallos DESPUES del review agresivo
  joinsBadJ : Nat := 0         -- joins con algun fallo antes de revisar
  joinsBadR : Nat := 0         -- ... y que el review NO arregla
  badRAt    : String := "-"
  /-- transitividad de la posesion, remedida con la ventana de 3 -/
  triTot    : Nat := 0
  triOk     : Nat := 0
  triBad    : Nat := 0
  deriving Repr

/-- `Descent.AllParentsOwn` contado: número de ternas (nodo, owner de arriba, padre) que fallan. -/
def apoFails (g : GPathM) (cap : Nat) : Nat := Id.run do
  let mut bad := 0
  for n in g.nodes do
    if n.id.id.step ≥ 1 && n.id.id.step < g.current_step then
      let vs := (n.owners.filter
        (fun v => decide (n.id.id.step ≤ v.id.step ∧ v.id.step < g.current_step))).take cap
      for v in vs do
        for c in n.parents do
          match g.node? c with
          | none => pure ()
          | some mc => if !mc.owners.contains v then bad := bad + 1
  return bad

/-- Transitividad de la posesión: si `u` está en la tabla de `v` y `v` en la de `w`, ¿está `u` en la
de `w`? Sobre owners que son nodos del estado, acotado por `cap`. -/
def transStats (g : GPathM) (cap : Nat) : Nat × Nat := Id.run do
  let mut tot := 0
  let mut ok := 0
  for w in g.nodes.take cap do
    for v in (w.owners.take cap) do
      match g.node? v with
      | none => pure ()
      | some mv =>
        for u in (mv.owners.take cap) do
          if u != v && u != w.id then
            tot := tot + 1
            if w.owners.contains u then ok := ok + 1
  return (tot, ok)

def measureJoin (A B J : GPathM) (label : String) (a : JAcc) : JAcc := Id.run do
  let mut a := { a with joins := a.joins + 1 }
  for n in A.nodes do
    match B.node? n.id with
    | none => pure ()
    | some m =>
      a := { a with merged := a.merged + 1 }
      let same := n.parents.all (fun p => m.parents.contains p)
        && m.parents.all (fun p => n.parents.contains p)
      if !same then
        a := { a with diffPar := a.diffPar + 1
                    , diffParAt := s!"{label} paso {n.id.id.step}: {n.parents.length} vs {m.parents.length} padres" }
  let fa := apoFails A 40
  let fb := apoFails B 40
  let fj := apoFails J 40
  let fr := apoFails (AggressiveReview.reviewAgg J) 40
  a := { a with apoA := a.apoA + fa, apoB := a.apoB + fb, apoJ := a.apoJ + fj, apoR := a.apoR + fr
              , joinsBadJ := a.joinsBadJ + (if fj > 0 then 1 else 0)
              , joinsBadR := a.joinsBadR + (if fr > 0 then 1 else 0) }
  if fr > 0 then
    a := { a with badRAt := s!"{label}: {fj} fallos antes de revisar, {fr} despues" }
  return a

def sendToJ (φ : Cnf) (label : String) (g : GPathM) (st : PureLine × JAcc) (d : NodeId) :
    PureLine × JAcc := Id.run do
  let (next, a0) := st
  let mut a := a0
  let h := upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
  if !isValid h then return (next, a)
  match next.find? (fun kv => kv.1 == d) with
  | some (_, existing) =>
    let j := doJoin existing h
    a := measureJoin existing h j s!"{label}→⟨{d.step},{d.index}⟩" a
    return (next.map (fun kv => if kv.1 == d then (d, j) else kv), a)
  | none => return (next ++ [(d, h)], a)

def advanceJ (φ : Cnf) (line : PureLine) (a : JAcc) : PureLine × JAcc :=
  line.foldl (fun st kv =>
    (mapSons φ kv.1.step kv.1.index).foldl (sendToJ φ s!"⟨{kv.1.step},{kv.1.index}⟩" kv.2) st)
    ((([] : PureLine)), a)

def runFormulaJ (φ : Cnf) (a : JAcc) : JAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for _ in [0:steps] do
    let (l', a') := advanceJ φ line a
    line := l'
    a := a'
    for kv in line do
      let (t, ok) := transStats kv.2 24
      a := { a with triTot := a.triTot + t, triOk := a.triOk + ok, triBad := a.triBad + (t - ok) }
  return a

def reportJ (name : String) (a : JAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, envios {a.sends}, de ellos JOINS: {a.joins}  ({pct a.joins a.sends})"
  IO.println s!"   nodos fusionados (en los dos lados): {a.merged}"
  IO.println s!"     con listas de padres DISTINTAS  : {a.diffPar}  ({pct a.diffPar a.merged})"
  if a.diffPar > 0 then IO.println s!"       primero: {a.diffParAt}"
  IO.println s!"   AllParentsOwn, fallos (nodo, owner de arriba, padre):"
  IO.println s!"     lado ya presente          : {a.apoA}"
  IO.println s!"     lado que llega            : {a.apoB}"
  IO.println s!"     la union, SIN revisar     : {a.apoJ}   (joins afectados: {a.joinsBadJ}/{a.joins})"
  IO.println s!"     DESPUES del review agresivo: {a.apoR}   (joins afectados: {a.joinsBadR}/{a.joins})"
  if a.joinsBadR > 0 then IO.println s!"       primero: {a.badRAt}"
  IO.println s!"   transitividad de la posesion, REMEDIDA con ventana 3 ({a.triTot} trios):"
  IO.println s!"     se cumple : {a.triOk}  ({pct a.triOk a.triTot})"
  IO.println s!"     FALLA     : {a.triBad}  ({pct a.triBad a.triTot})"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- ¿Deja el review solo nodos con camino? (`SupportedG`)
-- ============================================================

/-! La afirmacion es: *al aplicar el review sobre todo el grafo, solo quedan nodos con caminos
validos*. En el repo se llama `L6Up.SupportedG` y es el enunciado de cabecera: si fuera cierto,
un estado valido esta inhabitado y la maquina decide.

Esta sonda lo comprueba de frente: para cada nodo de cada estado busca una cadena completa que pase
por el —enlazada padre-hijo, con todos los picks poseyendose mutuamente y todos owners globales—
con retroceso y presupuesto acotado. Un nodo sin cadena es un **fantasma**. -/

structure SAcc where
  formulas : Nat := 0
  states   : Nat := 0
  nodes    : Nat := 0
  sup      : Nat := 0          -- tiene cadena: nodo real
  ghost    : Nat := 0          -- NO tiene cadena: fantasma
  out      : Nat := 0          -- presupuesto agotado, indeciso
  ghostAt  : String := "-"
  deriving Repr

/-- Una cadena completa por `x`: un nodo por paso, enlazados padre-hijo, todos owners globales y
poseyendose mutuamente. -/
partial def chainAt (g : GPathM) (x : PathNodeId) (budget : Nat) (picks : List PathNodeId) (k : Int) :
    Nat × Bool :=
  if budget == 0 then (0, false)
  else if k ≥ g.current_step then (budget, true)
  else
    let base : List PathNodeId :=
      match picks with
      | [] => g.gowners.filter (fun (c : PathNodeId) => c.id.step == k)
      | p :: _ => (sonsOf g p).filter (fun (c : PathNodeId) => c.id.step == k)
    let base := if k == x.id.step then base.filter (fun c => c == x) else base
    let cands := base.filter (fun c =>
      g.gowners.contains c && picks.all (fun p => mutuallyOwn g c p))
    cands.foldl (fun (st : Nat × Bool) c =>
      if st.2 then st else chainAt g x (st.1 - 1) (c :: picks) (k + 1)) (budget, false)

def scanSupport (label : String) (g : GPathM) (budget : Nat) (a : SAcc) : SAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for n in g.nodes do
    let (left, ok) := chainAt g n.id budget [] 0
    a := { a with nodes := a.nodes + 1 }
    if ok then a := { a with sup := a.sup + 1 }
    else if left == 0 then a := { a with out := a.out + 1 }
    else
      a := { a with ghost := a.ghost + 1
                  , ghostAt := s!"{label} paso {n.id.id.step}, {n.owners.length} owners, {n.parents.length} padres" }
  return a

/-- Sobre los estados de la linea final, que son los que el lector lee. -/
def runFormulaS (φ : Cnf) (budget : Nat) (a : SAcc) : SAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := scanSupport s!"⟨{kv.1.step},{kv.1.index}⟩" g budget a
  return a

/-- Y sobre TODOS los estados de TODAS las lineas, que es donde vive `SupportedG`. -/
def runFormulaSAll (φ : Cnf) (budget : Nat) (a : SAcc) : SAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for i in [0:steps] do
    line := pureAdvanceW φ line
    for kv in line do
      a := scanSupport s!"linea {i+1} ⟨{kv.1.step},{kv.1.index}⟩" kv.2 budget a
  return a

def reportS (name : String) (a : SAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, nodos {a.nodes}"
  IO.println s!"     con cadena (nodo real) : {a.sup}  ({pct a.sup a.nodes})"
  IO.println s!"     FANTASMA (sin cadena)  : {a.ghost}  ({pct a.ghost a.nodes})"
  IO.println s!"     indeciso (presupuesto) : {a.out}"
  if a.ghost > 0 then IO.println s!"     primero: {a.ghostAt}"
  IO.println s!"   SupportedG: {if a.ghost == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- ¿Afecta el filtro de requisitos a «todo nodo tiene camino»?
-- ============================================================

/-! `supportedS_reviewAgg` demuestra que la revision conserva `SupportedS`, y el `up` y el `doJoin`
tampoco pueden crear un fantasma. Queda el filtro. Esta sonda mide el envio en tres tiempos:

1. `g` — el estado de partida
2. `filterRequire` plegado sobre los requisitos duros, **antes de revisar**
3. y despues de `reviewAgg`

Si (2) ya sale a cero fantasmas, el filtro conserva `SupportedS` por si mismo y la intuicion es
literal. Si (2) tiene fantasmas y (3) no, entonces la revision es la que los quita, y el teorema
que falta es ese. -/

structure FAcc where
  formulas : Nat := 0
  sends    : Nat := 0
  nBefore  : Nat := 0          -- nodos antes del filtro
  gBefore  : Nat := 0          -- ... fantasmas
  nFilt    : Nat := 0          -- nodos tras `filterRequire`, SIN revisar
  gFilt    : Nat := 0          -- ... fantasmas
  nRev     : Nat := 0          -- nodos tras `reviewAgg`
  gRev     : Nat := 0          -- ... fantasmas
  sendsBad : Nat := 0          -- envios donde el filtro deja algun fantasma
  sendsRev : Nat := 0          -- ... que la revision NO arregla
  badAt    : String := "-"
  outs     : Nat := 0
  deriving Repr

def ghostCount (g : GPathM) (budget : Nat) : Nat × Nat × Nat := Id.run do
  let mut n := 0
  let mut gh := 0
  let mut ou := 0
  for m in g.nodes do
    n := n + 1
    let (left, ok) := chainAt g m.id budget [] 0
    if !ok then
      if left == 0 then ou := ou + 1 else gh := gh + 1
  return (n, gh, ou)

def sendToF2 (φ : Cnf) (label : String) (g : GPathM) (st : PureLine × FAcc) (d : NodeId) :
    PureLine × FAcc := Id.run do
  let (next, a0) := st
  let mut a := { a0 with sends := a0.sends + 1 }
  -- las tres fotos del envio
  let ws := filterWeakAll g (weakReqOfCnf φ d)
  let filt := (reqOfCnf φ d).foldl filterRequire ws
  let rev := AggressiveReview.reviewAgg filt
  -- solo cuentan los envios que SOBREVIVEN: un estado invalido tiene pasos sin owner global,
  -- asi que ningun nodo tiene cadena y contarlo no dice nada
  let alive := isValid rev
  let (n0, g0, o0) := if alive then ghostCount g 60000 else (0, 0, 0)
  let (n1, g1, o1) := if alive then ghostCount filt 60000 else (0, 0, 0)
  let (n2, g2, o2) := if alive then ghostCount rev 60000 else (0, 0, 0)
  a := { a with sends := a.sends + (if alive then 1 else 0)
              , nBefore := a.nBefore + n0, gBefore := a.gBefore + g0
              , nFilt := a.nFilt + n1, gFilt := a.gFilt + g1
              , nRev := a.nRev + n2, gRev := a.gRev + g2
              , outs := a.outs + o0 + o1 + o2
              , sendsBad := a.sendsBad + (if g1 > 0 then 1 else 0)
              , sendsRev := a.sendsRev + (if g2 > 0 then 1 else 0) }
  if g1 > 0 then
    a := { a with badAt := s!"{label}→⟨{d.step},{d.index}⟩: {g1} fantasmas tras filtrar, {g2} tras revisar" }
  -- y seguimos la corrida de verdad
  let h := upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
  if !isValid h then return (next, a)
  match next.find? (fun kv => kv.1 == d) with
  | some (_, existing) => return (next.map (fun kv => if kv.1 == d then (d, doJoin existing h) else kv), a)
  | none => return (next ++ [(d, h)], a)

def runFormulaF2 (φ : Cnf) (a : FAcc) : FAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for _ in [0:steps] do
    let (l', a') := line.foldl (fun st kv =>
      (mapSons φ kv.1.step kv.1.index).foldl (sendToF2 φ s!"⟨{kv.1.step},{kv.1.index}⟩" kv.2) st)
      ((([] : PureLine)), a)
    line := l'
    a := a'
  return a

def reportF2 (name : String) (a : FAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, envios que SOBREVIVEN {a.sends}"
  IO.println s!"   fantasmas (nodos sin cadena) en las tres fotos del envio:"
  IO.println s!"     1. antes del filtro            : {a.gBefore}/{a.nBefore}  ({pct a.gBefore a.nBefore})"
  IO.println s!"     2. tras filterRequire, SIN revisar: {a.gFilt}/{a.nFilt}  ({pct a.gFilt a.nFilt})"
  IO.println s!"     3. tras reviewAgg              : {a.gRev}/{a.nRev}  ({pct a.gRev a.nRev})"
  IO.println s!"   envios donde el filtro deja fantasmas : {a.sendsBad}/{a.sends}"
  IO.println s!"   ... que la revision NO arregla        : {a.sendsRev}/{a.sends}"
  if a.sendsBad > 0 then IO.println s!"     primero: {a.badAt}"
  IO.println s!"   indecisos (presupuesto): {a.outs}"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- `SoundAt (LitStep φ)`: ¿son realizables las entradas hacia pasos literales?
-- ============================================================

/-! `RunSteps.realizes_pin` demuestra la mitad dificil —tras un pin, todo nodo vivo esta en una
cadena del estado pinchado que pasa por el pin— bajo `SoundAt (LitStep φ) g`: *toda entrada de la
tabla que apunte a un paso literal (o al 0) es realizable por una cadena que pase por los dos*.

Eso es mucho menos que `TablesSound`: no pide nada de las entradas hacia pasos de clausula, que es
donde vive la no-transitividad medida (5-20%). Nunca se habia medido por separado. -/

structure AAcc where
  formulas : Nat := 0
  states   : Nat := 0
  entries  : Nat := 0          -- entradas (nodo, owner) hacia un paso literal o el 0
  real     : Nat := 0          -- ... realizables: hay cadena por los dos
  ghost    : Nat := 0          -- ... NO realizables: entrada fantasma
  out      : Nat := 0
  ghostAt  : String := "-"
  /-- contraste: las entradas hacia pasos de CLAUSULA -/
  cEntries : Nat := 0
  cReal    : Nat := 0
  cGhost   : Nat := 0
  deriving Repr

/-- Cadena completa que pasa por todos los nodos de `forced`. -/
partial def chainAt2 (g : GPathM) (forced : List PathNodeId) (budget : Nat)
    (picks : List PathNodeId) (k : Int) : Nat × Bool :=
  if budget == 0 then (0, false)
  else if k ≥ g.current_step then (budget, true)
  else
    let base : List PathNodeId :=
      match picks with
      | [] => g.gowners.filter (fun (c : PathNodeId) => c.id.step == k)
      | p :: _ => (sonsOf g p).filter (fun (c : PathNodeId) => c.id.step == k)
    let base := match forced.find? (fun (f : PathNodeId) => f.id.step == k) with
      | some f => base.filter (fun c => c == f)
      | none => base
    let cands := base.filter (fun c =>
      g.gowners.contains c && picks.all (fun p => mutuallyOwn g c p))
    cands.foldl (fun (st : Nat × Bool) c =>
      if st.2 then st else chainAt2 g forced (st.1 - 1) (c :: picks) (k + 1)) (budget, false)

def scanSoundAt (label : String) (lb : Int) (g : GPathM) (budget cap : Nat) (a : AAcc) :
    AAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for n in g.nodes.take cap do
    for w in n.owners.take cap do
      let lit := w.id.step < lb || w.id.step == 0
      let (left, ok) := chainAt2 g [n.id, w] budget [] 0
      if lit then
        a := { a with entries := a.entries + 1 }
        if ok then a := { a with real := a.real + 1 }
        else if left == 0 then a := { a with out := a.out + 1 }
        else
          a := { a with ghost := a.ghost + 1
                      , ghostAt := s!"{label}: nodo@{n.id.id.step} owner@{w.id.step}" }
      else
        a := { a with cEntries := a.cEntries + 1
                    , cReal := a.cReal + (if ok then 1 else 0)
                    , cGhost := a.cGhost + (if ok || left == 0 then 0 else 1) }
  return a

def runFormulaA (φ : Cnf) (a : AAcc) : AAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for i in [0:steps] do
    line := pureAdvanceW φ line
    for kv in line do
      a := scanSoundAt s!"linea {i+1} ⟨{kv.1.step},{kv.1.index}⟩" (litBlock φ) kv.2 40000 60 a
  return a

def reportA (name : String) (a : AAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}"
  IO.println s!"   SoundAt (LitStep): entradas hacia un paso LITERAL o el 0: {a.entries}"
  IO.println s!"     realizables (hay cadena por los dos) : {a.real}  ({pct a.real a.entries})"
  IO.println s!"     ENTRADA FANTASMA                     : {a.ghost}  ({pct a.ghost a.entries})"
  IO.println s!"     indeciso (presupuesto)               : {a.out}"
  if a.ghost > 0 then IO.println s!"     primero: {a.ghostAt}"
  IO.println s!"   SoundAt(LitStep): {if a.ghost == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   contraste, entradas hacia pasos de CLAUSULA: {a.cEntries}"
  IO.println s!"     realizables : {a.cReal}  ({pct a.cReal a.cEntries})"
  IO.println s!"     fantasma    : {a.cGhost}  ({pct a.cGhost a.cEntries})"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- ¿Posee todo nodo a todos sus ancestros? (`AncOwned`)
-- ============================================================

/-! La frase del autor sobre el diseño: *cuando se construye un nuevo nodo se le da la
compatibilidad con todos sus ancestros, siendo sus owners la union de los de sus padres*.
`AncestorOwned.ancOwned_addNode` demuestra que el `up` la conserva; esta sonda mide si la
conservan tambien el `doJoin` y la revision.

Importa porque `AncestorOwned.pairwiseOwned_of_ancOwned` la convierte de un tiron en
`SupportedRun.ChainPairwise`, que era el residuo entero de la ruta B. -/

structure NAcc where
  formulas : Nat := 0
  states   : Nat := 0
  nodes    : Nat := 0
  badNodes : Nat := 0          -- nodos con algun ancestro fuera de su tabla
  pairs    : Nat := 0          -- pares (nodo, ancestro estricto)
  bad      : Nat := 0          -- ... que NO estan en la tabla
  badAt    : String := "-"
  deriving Repr

/-- Los ancestros estrictos de `y`: padres iterados, sin repetir, acotado por el numero de pasos. -/
def ancestorsOf (g : GPathM) (y : PathNodeId) : List PathNodeId := Id.run do
  let mut frontier : List PathNodeId := [y]
  let mut acc : List PathNodeId := []
  for _ in [0:(g.current_step + 1).toNat] do
    let mut next : List PathNodeId := []
    for p in frontier do
      match g.node? p with
      | some n =>
        for c in n.parents do
          if !acc.contains c then
            acc := c :: acc
            next := c :: next
      | none => pure ()
    frontier := next
  return acc

def scanAnc (label : String) (g : GPathM) (a : NAcc) : NAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for n in g.nodes do
    let mut badHere := 0
    for c in ancestorsOf g n.id do
      a := { a with pairs := a.pairs + 1 }
      if !n.owners.contains c then
        badHere := badHere + 1
        let at' := s!"{label} nodo paso {n.id.id.step} ({n.parents.length} padres, {n.owners.length} owners), ancestro paso {c.id.step}"
        a := { a with bad := a.bad + 1, badAt := if a.bad == 0 then at' else a.badAt }
    a := { a with nodes := a.nodes + 1 }
    if badHere > 0 then a := { a with badNodes := a.badNodes + 1 }
  return a

/-- Sobre los estados que el lector lee. -/
def runFormulaN (φ : Cnf) (a : NAcc) : NAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := scanAnc s!"⟨{kv.1.step},{kv.1.index}⟩" g a
  return a

/-- Y sobre TODOS los estados de TODAS las lineas. -/
def runFormulaNAll (φ : Cnf) (a : NAcc) : NAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for i in [0:steps] do
    line := pureAdvanceW φ line
    for kv in line do
      a := scanAnc s!"linea {i+1} ⟨{kv.1.step},{kv.1.index}⟩" kv.2 a
  return a

def reportN (name : String) (a : NAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, nodos {a.nodes}"
  IO.println s!"   pares (nodo, ancestro) : {a.pairs}"
  IO.println s!"     ancestro EN la tabla : {a.pairs - a.bad}  ({pct (a.pairs - a.bad) a.pairs})"
  IO.println s!"     ancestro FUERA       : {a.bad}  ({pct a.bad a.pairs})"
  IO.println s!"   nodos con algun ancestro fuera: {a.badNodes}  ({pct a.badNodes a.nodes})"
  if a.bad > 0 then IO.println s!"     primero: {a.badAt}"
  IO.println s!"   AncOwned: {if a.bad == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

/-! **¿Donde nace el fallo?** El `up` real es
`up (filterAllAgg (filterWeakAll g ws) reqs) d`, y `addNode` va el ULTIMO —y ese paso esta
demostrado (`AncestorOwned.ancOwned_addNode`)—. Asi que el culpable solo puede ser el filtro+criba
de delante, o el `doJoin` que funde el envio con lo que ya habia. Esta sonda saca cuatro fotos por
envio y compara. -/

def measureAnc (g : GPathM) : Nat × Nat := Id.run do
  let mut tot := 0
  let mut bad := 0
  for n in g.nodes do
    for c in ancestorsOf g n.id do
      tot := tot + 1
      if !n.owners.contains c then bad := bad + 1
  return (tot, bad)

/-- Diagnostico del primer estado con fallo: cuantos ancestros que faltan NO son owner global,
cuantos no son nodo, y cuantos SI estan en la tabla de algun padre del nodo. -/
def diagAnc (g : GPathM) : String := Id.run do
  let mut bad := 0
  let mut noGow := 0
  let mut noNode := 0
  let mut inParent := 0
  let mut adjacent := 0
  let mut sample := ""
  for n in g.nodes do
    for c in ancestorsOf g n.id do
      if !n.owners.contains c then
        bad := bad + 1
        if !g.gowners.contains c then noGow := noGow + 1
        if (g.node? c).isNone then noNode := noNode + 1
        if n.parents.contains c then adjacent := adjacent + 1
        if n.parents.any (fun p => match g.node? p with
                                   | some mp => mp.owners.contains c
                                   | none => false) then inParent := inParent + 1
        if sample == "" then
          sample := s!"nodo@{n.id.id.step} ({n.parents.length} padres) ancestro@{c.id.step}"
  return s!"faltan {bad}: sin gowner {noGow}, sin nodo {noNode}, padre directo {adjacent}, en tabla de algun padre {inParent}; {sample}"

/-- Reconstruye la tabla de cada nodo **como la construye el `up`**: la union de las de sus padres,
recortada a `gowners`. De abajo arriba, para que lo añadido se propague. Es la regla de `rowOwners`
aplicada a un nodo que ya existe — que es justo lo que un nodo fusionado deberia ser. -/
def rebuildOwners (g : GPathM) : GPathM := Id.run do
  let mut g := g
  for k in intRange 1 (g.current_step - 1) do
    for id in ((g.line k).map (·.id)) do
      match g.node? id with
      | none => pure ()
      | some n =>
        let uni := (unionOwnersOf g n.parents).filter (fun q => g.gowners.contains q)
        let extra := uni.filter (fun q => !n.owners.contains q)
        if !extra.isEmpty then
          g := updateAt g id (fun m => { m with owners := m.owners ++ extra })
  return g

structure N4 where
  formulas    : Nat := 0
  sends       : Nat := 0
  joins       : Nat := 0
  tSrc  : Nat := 0
  bSrc  : Nat := 0
  tFil  : Nat := 0
  bFil  : Nat := 0
  tUp   : Nat := 0
  bUp   : Nat := 0
  tJoin : Nat := 0
  bJoin : Nat := 0
  tRev  : Nat := 0
  bRev  : Nat := 0
  tReb  : Nat := 0
  bReb  : Nat := 0
  rebBroke : Nat := 0
  sendsBadFil : Nat := 0
  sendsBadUp  : Nat := 0
  joinsBad    : Nat := 0
  filAt  : String := "-"
  joinAt : String := "-"
  diag   : String := "-"
  deriving Repr

def sendToN (φ : Cnf) (label : String) (g : GPathM) (st : PureLine × N4) (d : NodeId) :
    PureLine × N4 := Id.run do
  let (next, a0) := st
  let mut a := a0
  let ws := weakReqOfCnf φ d
  let rs := reqOfCnf φ d
  let h := upFilteringWeak g ws rs d ""
  if !isValid h then return (next, a)
  let f := AggressiveReview.filterAllAgg (filterWeakAll g ws) rs
  let (t0, b0) := measureAnc g
  let (t1, b1) := measureAnc f
  let (t2, b2) := measureAnc h
  a := { a with sends := a.sends + 1
              , tSrc := a.tSrc + t0, bSrc := a.bSrc + b0
              , tFil := a.tFil + t1, bFil := a.bFil + b1
              , tUp  := a.tUp  + t2, bUp  := a.bUp  + b2
              , sendsBadFil := a.sendsBadFil + (if b1 > b0 then 1 else 0)
              , sendsBadUp  := a.sendsBadUp  + (if b2 > b1 then 1 else 0)
              , filAt := if b1 > b0 && a.sendsBadFil == 0 then
                           s!"{label}→⟨{d.step},{d.index}⟩: {b0} antes, {b1} tras filtro+criba"
                         else a.filAt }
  match next.find? (fun kv => kv.1 == d) with
  | some (_, existing) =>
    let j := doJoin existing h
    let (_, be) := measureAnc existing
    let (tj, bj) := measureAnc j
    let (tr, br) := measureAnc (AggressiveReview.reviewAgg j)
    let jb := AggressiveReview.reviewAgg (rebuildOwners j)
    let (tb, bb) := measureAnc jb
    a := { a with joins := a.joins + 1
                , tJoin := a.tJoin + tj, bJoin := a.bJoin + bj
                , tRev := a.tRev + tr, bRev := a.bRev + br
                , tReb := a.tReb + tb, bReb := a.bReb + bb
                , rebBroke := a.rebBroke + (if isValid jb then 0 else 1)
                , diag := if bj > be + b2 && a.diag == "-" then diagAnc j else a.diag
                , joinsBad := a.joinsBad + (if bj > be + b2 then 1 else 0)
                , joinAt := if bj > be + b2 && a.joinsBad == 0 then
                              s!"{label}→⟨{d.step},{d.index}⟩: {be}+{b2} en los dos lados, {bj} tras el join"
                            else a.joinAt }
    return (next.map (fun kv => if kv.1 == d then (d, j) else kv), a)
  | none => return (next ++ [(d, h)], a)

def advanceN (φ : Cnf) (line : PureLine) (a : N4) : PureLine × N4 :=
  line.foldl (fun st kv =>
    (mapSons φ kv.1.step kv.1.index).foldl (sendToN φ s!"⟨{kv.1.step},{kv.1.index}⟩" kv.2) st)
    ((([] : PureLine)), a)

def runFormulaN4 (φ : Cnf) (a : N4) : N4 := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  let steps := (stepCount φ - 1).toNat
  for _ in [0:steps] do
    let (l', a') := advanceN φ line a
    line := l'
    a := a'
  return a

def reportN4 (name : String) (a : N4) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, envios {a.sends}, de ellos JOINS: {a.joins}"
  IO.println s!"   ancestros FUERA de la tabla, por foto:"
  IO.println s!"     1. estado de partida       : {a.bSrc} / {a.tSrc}  ({pct a.bSrc a.tSrc})"
  IO.println s!"     2. tras filtro + criba     : {a.bFil} / {a.tFil}  ({pct a.bFil a.tFil})"
  IO.println s!"     3. tras addNode (el up)    : {a.bUp} / {a.tUp}  ({pct a.bUp a.tUp})"
  IO.println s!"     4. tras doJoin             : {a.bJoin} / {a.tJoin}  ({pct a.bJoin a.tJoin})"
  IO.println s!"     5. join + reviewAgg        : {a.bRev} / {a.tRev}  ({pct a.bRev a.tRev})"
  IO.println s!"     6. join + tabla del up + review: {a.bReb} / {a.tReb}  ({pct a.bReb a.tReb})"
  IO.println s!"        (de esos, estados que la reconstruccion invalida: {a.rebBroke})"
  IO.println s!"   envios donde el filtro+criba EMPEORA : {a.sendsBadFil}/{a.sends}"
  if a.sendsBadFil > 0 then IO.println s!"     primero: {a.filAt}"
  IO.println s!"   envios donde addNode EMPEORA         : {a.sendsBadUp}/{a.sends}"
  IO.println s!"   joins que CREAN ancestros sin tabla  : {a.joinsBad}/{a.joins}"
  if a.joinsBad > 0 then IO.println s!"     primero: {a.joinAt}"
  IO.println s!"   diagnostico: {a.diag}"
  IO.println s!"   ({ms} ms)"

-- ============================================================
-- `PinReachable`: ¿todo pin valido tiene cadena por el?
-- ============================================================

/-! `ReaderChain.readerVerdictW_of_pinReachable` reduce el lector sin retroceso a **una frase sobre
un estado y un pin**: si pinchar `mid` deja el grafo valido, alguna cadena completa del estado de
antes pasa por `mid`.

Es el residuo con su tamano correcto — mucho menos que `SupportedS`, que pedia una cadena por
NODO de cada estado. Esta sonda lo recorre: para cada estado que el lector visita, para cada
candidato del primer paso con eleccion, si el pin deja el grafo valido se busca una cadena completa
del estado de antes que pase por ese nodo. -/

structure PAcc where
  formulas : Nat := 0
  states   : Nat := 0
  pins     : Nat := 0          -- candidatos probados
  valid    : Nat := 0          -- ... que dejan el grafo valido
  withChain: Nat := 0          -- ... y tienen cadena por ellos
  noChain  : Nat := 0          -- ... y NO la tienen: contraejemplo a PinReachable
  out      : Nat := 0
  badAt    : String := "-"
  deriving Repr

def scanPinReach (label : String) (g : GPathM) (budget : Nat) (a : PAcc) : PAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  match ReaderExec.firstChoice g with
  | none => return a
  | some k =>
    for q in ownersAt g.gowners k do
      a := { a with pins := a.pins + 1 }
      if isValid (filterAllAgg g [q.id]) then
        a := { a with valid := a.valid + 1 }
        let (left, ok) := chainAt2 g [q] budget [] 0
        if ok then a := { a with withChain := a.withChain + 1 }
        else if left == 0 then a := { a with out := a.out + 1 }
        else
          a := { a with noChain := a.noChain + 1
                      , badAt := if a.noChain == 0 then s!"{label} paso {k}" else a.badAt }
    return a

/-- Recorre la trayectoria real del lector sin retroceso desde la semilla. -/
partial def walkPinReach (label : String) (g : GPathM) (fuel budget : Nat) (a : PAcc) : PAcc :=
  if fuel == 0 then a
  else
    let a := scanPinReach label g budget a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkPinReach label (filterAllAgg g [q.id]) (fuel - 1) budget a

def runFormulaP (φ : Cnf) (budget : Nat) (a : PAcc) : PAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkPinReach s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat budget a
  return a

def reportP (name : String) (a : PAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados de la lectura {a.states}, candidatos {a.pins}"
  IO.println s!"   pines que dejan el grafo VALIDO: {a.valid}  ({pct a.valid a.pins})"
  IO.println s!"     con cadena completa por el : {a.withChain}  ({pct a.withChain a.valid})"
  IO.println s!"     SIN cadena (contraejemplo) : {a.noChain}  ({pct a.noChain a.valid})"
  IO.println s!"     indeciso (presupuesto)     : {a.out}"
  if a.noChain > 0 then IO.println s!"     primero: {a.badAt}"
  IO.println s!"   PinReachable: {if a.noChain == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

/-! **`TablesSound` a lo largo de la lectura.** Es la hipotesis exacta de
`ReaderChain.readerVerdictW_of_tablesSound`: toda entrada de toda tabla de todo estado que el
lector visita es realizable. `scanSoundAt` con `lb = current_step` cuenta TODAS las entradas, no
solo las del bloque literal. -/

partial def walkTS (label : String) (g : GPathM) (fuel : Nat) (a : AAcc) : AAcc :=
  if fuel == 0 then a
  else
    let a := scanSoundAt label g.current_step g 40000 60 a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkTS label (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaTS (φ : Cnf) (a : AAcc) : AAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkTS s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat a
  return a

/-! **¿Es unico el nodo del paso 0?** Si lo fuera, toda cadena pasaria por el, y
`ReaderChain.RootPairSound` —«hay cadena por la raiz Y por `w`»— se volveria «hay cadena por `w`»:
un enunciado sobre UN nodo, que es el lado bueno de la frontera 2-vs-3.

`pureInit` arranca cada semilla de una sola raiz (`initSeed`), y el `up` nunca toca el paso 0. El
unico que puede meter dos es el `doJoin`, que funde dos estados que pueden venir de raices
distintas. -/

structure RAcc where
  formulas : Nat := 0
  states   : Nat := 0
  one      : Nat := 0          -- un solo nodo en el paso 0
  many     : Nat := 0          -- dos o mas
  maxRoots : Nat := 0
  rootOwn1 : Nat := 0          -- owners del paso 0 en la tabla de la raiz: uno
  rootOwnN : Nat := 0          -- ... dos o mas
  entries  : Nat := 0          -- (nodo, owner en el paso 0) sobre todos los nodos
  entries1 : Nat := 0          -- ... nodos con UN solo owner en el paso 0
  entriesN : Nat := 0          -- ... con dos o mas
  deriving Repr

def scanRoots (g : GPathM) (a : RAcc) : RAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  let roots := (g.line 0).length
  a := { a with one := a.one + (if roots == 1 then 1 else 0)
              , many := a.many + (if roots > 1 then 1 else 0)
              , maxRoots := if roots > a.maxRoots then roots else a.maxRoots }
  for n in g.nodes do
    let z := (ownersAt n.owners 0).length
    a := { a with entries := a.entries + z
                , entries1 := a.entries1 + (if z == 1 then 1 else 0)
                , entriesN := a.entriesN + (if z > 1 then 1 else 0) }
    if n.id.id.step == 0 then
      a := { a with rootOwn1 := a.rootOwn1 + (if z == 1 then 1 else 0)
                  , rootOwnN := a.rootOwnN + (if z > 1 then 1 else 0) }
  return a

partial def walkRoots (g : GPathM) (fuel : Nat) (a : RAcc) : RAcc :=
  if fuel == 0 then a
  else
    let a := scanRoots g a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkRoots (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaR (φ : Cnf) (allStates : Bool) (a : RAcc) : RAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  if allStates then
    let mut line : PureLine := pureInit φ
    let steps := (stepCount φ - 1).toNat
    for _ in [0:steps] do
      line := pureAdvanceW φ line
      for kv in line do
        a := scanRoots kv.2 a
  else
    for kv in pureRunW φ do
      let g := filterAllAgg kv.2 []
      if isValid g then
        a := walkRoots g (stepCount φ).toNat a
  return a

def reportR (name : String) (a : RAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}"
  IO.println s!"   nodos en el paso 0:  uno {a.one}  ({pct a.one a.states})   dos o mas {a.many}   max {a.maxRoots}"
  IO.println s!"   owners del paso 0 en la tabla de la RAIZ: uno {a.rootOwn1}, dos o mas {a.rootOwnN}"
  IO.println s!"   owners del paso 0 por nodo (todos los nodos): uno {a.entries1}, dos o mas {a.entriesN}"
  IO.println s!"   raiz unica: {if a.many == 0 then "SI en lo medido" else "NO"}"
  IO.println s!"   ({ms} ms)"

/-! **El descenso para PARES.** `PinPairSound` pide una cadena por `x` y por `q`. La semilla es
gratis: `AggOk` da un owner comun de los dos en el paso de arriba, y por simetria ese owner los
posee a los dos. Lo que falta es el PASO: dado un nodo `d` que posee a `x` y a `q`, ¿hay un PADRE de
`d` que tambien los posee a los dos?

Eso es `Descent.PairMeet` restringido al par que estoy descendiendo. Si se cumple, la prueba es un
descenso avido y no hace falta buscar. Si falla, la prueba tiene que ser un argumento de busqueda, y
conviene saberlo antes de intentarla. -/

structure DPAcc where
  formulas : Nat := 0
  states   : Nat := 0
  pairs    : Nat := 0          -- pares (x,q) que se poseen mutuamente
  seeds    : Nat := 0          -- ... con semilla arriba (AggOk)
  cells    : Nat := 0          -- (par, nodo d que posee a los dos, d.step > 0)
  cellsOk  : Nat := 0          -- ... con ALGUN padre que posee a los dos
  cellsBad : Nat := 0          -- ... SIN ninguno: el descenso avido se atasca
  multi    : Nat := 0          -- ... con dos o mas padres asi
  badAt    : String := "-"
  /-- el descenso de verdad, desde la semilla -/
  dTried   : Nat := 0
  dOk      : Nat := 0          -- con retroceso, llega al paso 0
  dStuck   : Nat := 0          -- ni con retroceso
  dGreedy  : Nat := 0          -- el avido puro (primer candidato) llega al 0
  dOut     : Nat := 0
  /-- el descenso CON REVIEW en el bucle, que es lo que hace el lector -/
  rTried   : Nat := 0
  rValid   : Nat := 0          -- pinchar x y q deja el grafo valido
  rOk      : Nat := 0          -- ... y el descenso avido CON REVIEW llega arriba
  rBad     : Nat := 0          -- ... y NO llega: haria falta retroceso
  rBadAt   : String := "-"
  deriving Repr

def ownsBoth (g : GPathM) (c x q : PathNodeId) : Bool :=
  match g.node? c with
  | some n => n.owners.contains x && n.owners.contains q
  | none => false

/-- El descenso de verdad: desde `cur`, bajando por padres que poseen a `x` y a `q`. -/
partial def pairDescend (g : GPathM) (x q cur : PathNodeId) (budget : Nat) : Nat × Bool :=
  if budget == 0 then (0, false)
  else if cur.id.step ≤ 0 then (budget, true)
  else
    let cands := (match g.node? cur with | some n => n.parents | none => []).filter
      (fun c => ownsBoth g c x q)
    cands.foldl (fun (st : Nat × Bool) c =>
      if st.2 then st else pairDescend g x q c (st.1 - 1)) (budget, false)

/-- El mismo, sin retroceso: siempre el primer candidato. -/
partial def pairDescendGreedy (g : GPathM) (x q cur : PathNodeId) (fuel : Nat) : Bool :=
  if fuel == 0 then false
  else if cur.id.step ≤ 0 then true
  else
    match ((match g.node? cur with | some n => n.parents | none => []).find?
      (fun c => ownsBoth g c x q)) with
    | none => false
    | some c => pairDescendGreedy g x q c (fuel - 1)

/-- **El descenso como lo hace el lector**: en cada paso elige un candidato que sobreviva al pin, y
**revisa todo el grafo** antes de seguir. Avido puro: el primero que deja el grafo valido, sin
retroceso nunca. -/
partial def descendReviewed (g : GPathM) (x q : PathNodeId) (k : Int) (fuel : Nat) : Bool :=
  if fuel == 0 then false
  else if k ≥ g.current_step then true
  else
    match (ownersAt g.gowners k).find? (fun c => isValid (filterAllAgg g [c.id])) with
    | none => false
    | some c => descendReviewed (filterAllAgg g [c.id]) x q (k + 1) (fuel - 1)

def scanPairDescent (label : String) (g : GPathM) (cap : Nat) (a : DPAcc) : DPAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for nx in g.nodes.take cap do
    let x := nx.id
    for q in (nx.owners.take cap) do
      if q != x && ownsBoth g x x q && ownsBoth g q x q then
        a := { a with pairs := a.pairs + 1 }
        let top := g.gowners.filter (fun c =>
          c.id.step == g.current_step - 1 && ownsBoth g c x q)
        if !top.isEmpty then a := { a with seeds := a.seeds + 1 }
        -- el descenso de verdad, desde cualquier semilla
        a := { a with dTried := a.dTried + 1 }
        let (left, ok) := top.foldl (fun (st : Nat × Bool) t =>
          if st.2 then st else pairDescend g x q t (st.1 - 1)) (20000, false)
        if ok then a := { a with dOk := a.dOk + 1 }
        else if left == 0 then a := { a with dOut := a.dOut + 1 }
        else a := { a with dStuck := a.dStuck + 1 }
        if top.any (fun t => pairDescendGreedy g x q t (g.current_step + 1).toNat) then
          a := { a with dGreedy := a.dGreedy + 1 }
        -- y ahora como lo hace el lector: pinchar los dos, revisar, y bajar revisando
        a := { a with rTried := a.rTried + 1 }
        let h := filterAllAgg g [x.id, q.id]
        if isValid h then
          a := { a with rValid := a.rValid + 1 }
          if descendReviewed h x q 0 (g.current_step + 2).toNat then
            a := { a with rOk := a.rOk + 1 }
          else
            a := { a with rBad := a.rBad + 1
                        , rBadAt := if a.rBad == 0 then s!"{label} x@{x.id.step} q@{q.id.step}"
                                    else a.rBadAt }
        -- el paso: todo nodo que posee a los dos, ¿tiene un padre que tambien?
        for nd in g.nodes do
          if nd.id.id.step > 0 && nd.owners.contains x && nd.owners.contains q then
            let good := nd.parents.filter (fun c => ownsBoth g c x q)
            a := { a with cells := a.cells + 1 }
            if good.isEmpty then
              a := { a with cellsBad := a.cellsBad + 1
                          , badAt := if a.cellsBad == 0 then
                              s!"{label} d@{nd.id.id.step} ({nd.parents.length} padres), x@{x.id.step}, q@{q.id.step}"
                            else a.badAt }
            else
              a := { a with cellsOk := a.cellsOk + 1
                          , multi := a.multi + (if good.length > 1 then 1 else 0) }
  return a

partial def walkPD (label : String) (g : GPathM) (fuel cap : Nat) (a : DPAcc) : DPAcc :=
  if fuel == 0 then a
  else
    let a := scanPairDescent label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkPD label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaPD (φ : Cnf) (cap : Nat) (a : DPAcc) : DPAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkPD s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat cap a
  return a

def reportPD (name : String) (a : DPAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, pares mutuos {a.pairs}"
  IO.println s!"   semilla arriba (AggOk) : {a.seeds}  ({pct a.seeds a.pairs})"
  IO.println s!"   el PASO, {a.cells} celdas (par, nodo que posee a los dos):"
  IO.println s!"     con padre que posee a los dos : {a.cellsOk}  ({pct a.cellsOk a.cells})"
  IO.println s!"     SIN ninguno (avido se atasca) : {a.cellsBad}  ({pct a.cellsBad a.cells})"
  IO.println s!"     con dos o mas padres asi      : {a.multi}  ({pct a.multi a.cells})"
  if a.cellsBad > 0 then IO.println s!"     primero: {a.badAt}"
  IO.println s!"   el DESCENSO de verdad, {a.dTried} pares:"
  IO.println s!"     llega al paso 0 (con retroceso) : {a.dOk}  ({pct a.dOk a.dTried})"
  IO.println s!"     NI con retroceso                : {a.dStuck}  ({pct a.dStuck a.dTried})"
  IO.println s!"     llega sin retroceso (avido)     : {a.dGreedy}  ({pct a.dGreedy a.dTried})"
  IO.println s!"     indeciso (presupuesto)          : {a.dOut}"
  IO.println s!"   descenso por pares (SIN review): {if a.dStuck == 0 then "SE CUMPLE" else "FALLA"}"
  IO.println s!"   ── y ahora COMO LO HACE EL LECTOR, revisando en cada paso, {a.rTried} pares:"
  IO.println s!"     pinchar x y q deja el grafo valido : {a.rValid}  ({pct a.rValid a.rTried})"
  IO.println s!"       y el avido CON REVIEW llega arriba : {a.rOk}  ({pct a.rOk a.rValid})"
  IO.println s!"       NO llega (haria falta retroceso)   : {a.rBad}  ({pct a.rBad a.rValid})"
  if a.rBad > 0 then IO.println s!"       primero: {a.rBadAt}"
  IO.println s!"   descenso CON review: {if a.rBad == 0 then "SIN RETROCESO en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

/-! **¿Pierde un nodo su propia tabla al pincharse?**

`ReaderChain.PinKeepsPartner` pide que tras pinchar `x` y revisar, `q` siga en la tabla de `x`. El
pin en si no quita nada -`filterRequire` solo reescribe `gowners`-, asi que todo depende del review.

Y la intuicion del diseño es fuerte: **todo lo que esta en la tabla de `x` es compatible con `x`**,
asi que pinchar `x` no deberia poder quitarselo. Esta sonda lo comprueba de frente. -/

structure OTAcc where
  formulas : Nat := 0
  states   : Nat := 0
  nodes    : Nat := 0
  valid    : Nat := 0          -- pinchar x deja el grafo valido
  gone     : Nat := 0          -- ... y x ya no esta
  entries  : Nat := 0          -- entradas de la tabla de x (fuera de su propio paso)
  kept     : Nat := 0          -- ... que sobreviven
  lost     : Nat := 0          -- ... que se pierden
  nodesBad : Nat := 0          -- nodos que pierden alguna
  lostAt   : String := "-"
  deriving Repr

def scanOwnTable (label : String) (g : GPathM) (cap : Nat) (a : OTAcc) : OTAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for nx in g.nodes.take cap do
    let x := nx.id
    a := { a with nodes := a.nodes + 1 }
    let h := filterAllAgg g [x.id]
    if isValid h then
      a := { a with valid := a.valid + 1 }
      match h.node? x with
      | none => a := { a with gone := a.gone + 1 }
      | some nx' =>
        let mut bad := 0
        for u in nx.owners do
          if u.id.step != x.id.step then
            a := { a with entries := a.entries + 1 }
            if nx'.owners.contains u then a := { a with kept := a.kept + 1 }
            else
              bad := bad + 1
              a := { a with lost := a.lost + 1
                          , lostAt := if a.lost == 0 then
                              s!"{label} x@{x.id.step} pierde owner@{u.id.step}" else a.lostAt }
        if bad > 0 then a := { a with nodesBad := a.nodesBad + 1 }
  return a

partial def walkOT (label : String) (g : GPathM) (fuel cap : Nat) (a : OTAcc) : OTAcc :=
  if fuel == 0 then a
  else
    let a := scanOwnTable label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkOT label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaOT (φ : Cnf) (cap : Nat) (a : OTAcc) : OTAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkOT s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat cap a
  return a

def reportOT (name : String) (a : OTAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, nodos probados {a.nodes}"
  IO.println s!"   pinchar el propio nodo deja el grafo valido: {a.valid}  ({pct a.valid a.nodes})"
  IO.println s!"     y el nodo desaparece: {a.gone}"
  IO.println s!"   entradas de su tabla (fuera de su paso): {a.entries}"
  IO.println s!"     sobreviven  : {a.kept}  ({pct a.kept a.entries})"
  IO.println s!"     SE PIERDEN  : {a.lost}  ({pct a.lost a.entries})"
  IO.println s!"   nodos que pierden alguna: {a.nodesBad}  ({pct a.nodesBad a.valid})"
  if a.lost > 0 then IO.println s!"     primero: {a.lostAt}"
  IO.println s!"   la tabla sobrevive a su propio pin: {if a.lost == 0 then "SI en lo medido" else "NO"}"
  IO.println s!"   ({ms} ms)"

/-! **`HopDown`**: lo que un padre posee por debajo de su paso, ¿lo posee el hijo?

Es la regla del `up` (`rowOwners` = union de los owners de los padres, intersecada con `gowners`)
leida como invariante del estado. Es estrictamente mas debil que `AncOwned`, que pedia lo mismo para
todos los ancestros y se midio falsa en el 22,8% de las fusiones: esta solo habla de **padres
directos**. Se mide sobre los estados de la linea final y sobre la trayectoria real del lector. -/

structure HDAcc where
  formulas : Nat := 0
  states   : Nat := 0
  pairs    : Nat := 0          -- (nodo, padre)
  cells    : Nat := 0          -- (nodo, padre, owner del padre por debajo)
  ok       : Nat := 0          -- ... que esta en la tabla del hijo
  bad      : Nat := 0          -- ... que NO esta
  nodesBad : Nat := 0
  firstBad : String := "-"
  deriving Repr

def scanHopDown (label : String) (g : GPathM) (cap : Nat) (a : HDAcc) : HDAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for ny in g.nodes.take cap do
    let mut nodeBad := 0
    for p in ny.parents do
      match g.node? p with
      | none => pure ()
      | some np =>
        a := { a with pairs := a.pairs + 1 }
        for w in np.owners do
          if w.id.step < p.id.step then
            a := { a with cells := a.cells + 1 }
            if ny.owners.contains w then
              a := { a with ok := a.ok + 1 }
            else
              let fb := if a.bad == 0 then
                  s!"{label} hijo@{ny.id.id.step} padre@{p.id.step} owner@{w.id.step}"
                else a.firstBad
              nodeBad := nodeBad + 1
              a := { a with bad := a.bad + 1, firstBad := fb }
    if nodeBad > 0 then a := { a with nodesBad := a.nodesBad + 1 }
  return a

partial def walkHD (label : String) (g : GPathM) (fuel cap : Nat) (a : HDAcc) : HDAcc :=
  if fuel == 0 then a
  else
    let a := scanHopDown label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkHD label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaHD (φ : Cnf) (cap : Nat) (a : HDAcc) : HDAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkHD s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat cap a
  return a

def reportHD (name : String) (a : HDAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, pares (nodo,padre) {a.pairs}"
  IO.println s!"   celdas (nodo, padre, owner del padre por debajo): {a.cells}"
  IO.println s!"     el hijo lo posee    : {a.ok}  ({pct a.ok a.cells})"
  IO.println s!"     NO lo posee         : {a.bad}  ({pct a.bad a.cells})"
  IO.println s!"   nodos con algun fallo : {a.nodesBad}"
  if a.bad > 0 then IO.println s!"     primero: {a.firstBad}"
  IO.println s!"   HopDown: {if a.bad == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

/-! **`HopDown` restringido**, que es el que el teorema usa de verdad: los tres nodos implicados
—el hijo, el padre y el owner— estan todos en la tabla de un mismo nodo `a`, porque en
`mem_owners_up` los tres son nodos de la cadena que vive dentro de la tabla de `a`. -/

structure HD2Acc where
  formulas : Nat := 0
  states   : Nat := 0
  cells    : Nat := 0
  ok       : Nat := 0
  bad      : Nat := 0
  firstBad : String := "-"
  deriving Repr

def scanHopDown2 (label : String) (g : GPathM) (cap : Nat) (a : HD2Acc) : HD2Acc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for na in g.nodes.take cap do
    for y in na.owners do
      match g.node? y with
      | none => pure ()
      | some ny =>
        for p in ny.parents do
          if na.owners.contains p then
            match g.node? p with
            | none => pure ()
            | some np =>
              for w in np.owners do
                if w.id.step < p.id.step && na.owners.contains w then
                  a := { a with cells := a.cells + 1 }
                  if ny.owners.contains w then
                    a := { a with ok := a.ok + 1 }
                  else
                    let fb := if a.bad == 0 then
                        s!"{label} a@{na.id.id.step} hijo@{y.id.step} padre@{p.id.step} owner@{w.id.step}"
                      else a.firstBad
                    a := { a with bad := a.bad + 1, firstBad := fb }
  return a

partial def walkHD2 (label : String) (g : GPathM) (fuel cap : Nat) (a : HD2Acc) : HD2Acc :=
  if fuel == 0 then a
  else
    let a := scanHopDown2 label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkHD2 label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaHD2 (φ : Cnf) (cap : Nat) (a : HD2Acc) : HD2Acc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkHD2 s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat cap a
  return a

def reportHD2 (name : String) (a : HD2Acc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}"
  IO.println s!"   celdas (a, hijo, padre, owner) todos en la tabla de a: {a.cells}"
  IO.println s!"     el hijo lo posee : {a.ok}  ({pct a.ok a.cells})"
  IO.println s!"     NO lo posee      : {a.bad}  ({pct a.bad a.cells})"
  if a.bad > 0 then IO.println s!"     primero: {a.firstBad}"
  IO.println s!"   HopDown restringido: {if a.bad == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

/-! **¿Es la tabla de un nodo una clique bajo la posesion?** Si dos entradas cualesquiera de la
tabla de `a`, en pasos distintos, se poseen mutuamente, entonces `TableChainOwned` es inmediato y
con ella toda la escalera. Es la pregunta de fondo de `DistantOwned`. -/

structure CQAcc where
  formulas : Nat := 0
  states   : Nat := 0
  tables   : Nat := 0
  pairs    : Nat := 0
  ok       : Nat := 0
  bad      : Nat := 0
  badAdj   : Nat := 0          -- fallos entre pasos CONTIGUOS (deberian ser 0)
  firstBad : String := "-"
  deriving Repr

def scanClique (label : String) (g : GPathM) (cap : Nat) (a : CQAcc) : CQAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for na in g.nodes.take cap do
    a := { a with tables := a.tables + 1 }
    for u in na.owners do
      for v in na.owners do
        if u.id.step != v.id.step then
          match g.node? v with
          | none => pure ()
          | some nv =>
            a := { a with pairs := a.pairs + 1 }
            if nv.owners.contains u then
              a := { a with ok := a.ok + 1 }
            else
              let adj := u.id.step == v.id.step + 1 || v.id.step == u.id.step + 1
              let fb := if a.bad == 0 then
                  s!"{label} a@{na.id.id.step} u@{u.id.step} v@{v.id.step}"
                else a.firstBad
              let nadj := if adj then a.badAdj + 1 else a.badAdj
              a := { a with bad := a.bad + 1, firstBad := fb, badAdj := nadj }
  return a

partial def walkCQ (label : String) (g : GPathM) (fuel cap : Nat) (a : CQAcc) : CQAcc :=
  if fuel == 0 then a
  else
    let a := scanClique label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkCQ label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaCQ (φ : Cnf) (cap : Nat) (a : CQAcc) : CQAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkCQ s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat cap a
  return a

def reportCQ (name : String) (a : CQAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, tablas {a.tables}"
  IO.println s!"   pares (u,v) de una misma tabla en pasos distintos: {a.pairs}"
  IO.println s!"     se poseen    : {a.ok}  ({pct a.ok a.pairs})"
  IO.println s!"     NO se poseen : {a.bad}  ({pct a.bad a.pairs})"
  IO.println s!"       de ellos contiguos : {a.badAdj}"
  if a.bad > 0 then IO.println s!"     primero: {a.firstBad}"
  IO.println s!"   la tabla es clique: {if a.bad == 0 then "SI en lo medido" else "NO"}"
  IO.println s!"   ({ms} ms)"

/-! **`TableChainOwned`, medido de verdad.** La tabla de un nodo no es clique (sonda `clique`,
7,9% de pares no se poseen), pero eso no decide nada: la hipotesis pide una cadena **enlazada por
padres** dentro de la tabla, no una seleccion cualquiera. Esta sonda construye esa cadena
—descenso ávido por enlaces de padre sin salir de la tabla de `a`— y comprueba si sus pares
distantes se poseen. -/

structure TCAcc where
  formulas : Nat := 0
  states   : Nat := 0
  tables   : Nat := 0
  chains   : Nat := 0          -- tablas en las que el descenso llega al paso 0
  stuck    : Nat := 0          -- ... en las que se atasca
  pairs    : Nat := 0
  ok       : Nat := 0
  bad      : Nat := 0
  firstBad : String := "-"
  deriving Repr

partial def descendInTable (g : GPathM) (na : PNodeM) (k : Int) (cur : PathNodeId)
    (acc : List PathNodeId) : Option (List PathNodeId) :=
  if k < 0 then some acc
  else
    match g.node? cur with
    | none => none
    | some nc =>
      match (ownersAt na.owners k).find? (fun u => nc.parents.contains u) with
      | none => none
      | some u => descendInTable g na (k - 1) u (u :: acc)

def tableChain (g : GPathM) (na : PNodeM) : Option (List PathNodeId) :=
  match (ownersAt na.owners (g.current_step - 1)).head? with
  | none => none
  | some t => descendInTable g na (g.current_step - 2) t [t]

def scanTableChain (label : String) (g : GPathM) (cap : Nat) (a : TCAcc) : TCAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for na in g.nodes.take cap do
    a := { a with tables := a.tables + 1 }
    match tableChain g na with
    | none => a := { a with stuck := a.stuck + 1 }
    | some ch =>
      a := { a with chains := a.chains + 1 }
      for u in ch do
        for v in ch do
          if u.id.step != v.id.step then
            match g.node? v with
            | none => pure ()
            | some nv =>
              a := { a with pairs := a.pairs + 1 }
              if nv.owners.contains u then
                a := { a with ok := a.ok + 1 }
              else
                let fb := if a.bad == 0 then
                    s!"{label} a@{na.id.id.step} u@{u.id.step} v@{v.id.step}"
                  else a.firstBad
                a := { a with bad := a.bad + 1, firstBad := fb }
  return a

partial def walkTC (label : String) (g : GPathM) (fuel cap : Nat) (a : TCAcc) : TCAcc :=
  if fuel == 0 then a
  else
    let a := scanTableChain label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkTC label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaTC (φ : Cnf) (cap : Nat) (a : TCAcc) : TCAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkTC s!"⟨{kv.1.step},{kv.1.index}⟩" g (stepCount φ).toNat cap a
  return a

def reportTC (name : String) (a : TCAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, tablas {a.tables}"
  IO.println s!"   el descenso por padres dentro de la tabla llega al paso 0: {a.chains}  ({pct a.chains a.tables})"
  IO.println s!"     se atasca: {a.stuck}"
  IO.println s!"   pares (u,v) de esa cadena en pasos distintos: {a.pairs}"
  IO.println s!"     se poseen    : {a.ok}  ({pct a.ok a.pairs})"
  IO.println s!"     NO se poseen : {a.bad}  ({pct a.bad a.pairs})"
  if a.bad > 0 then IO.println s!"     primero: {a.firstBad}"
  IO.println s!"   TableChainOwned: {if a.bad == 0 then "SE CUMPLE en lo medido" else "FALLA"}"
  IO.println s!"   ({ms} ms)"

/-! **¿Cuanto cubre `mem_owners_of_singleAt`?** Cierra el par `(u,v)` de la cadena de la tabla de `a`
cuando la tabla de `a` tiene **un solo** id en el paso de `u`. Esta sonda lo cuenta sobre las mismas
cadenas que mide `tablechain`. -/

structure TCSAcc where
  formulas : Nat := 0
  states   : Nat := 0
  tables   : Nat := 0
  pairs    : Nat := 0
  single   : Nat := 0          -- un solo id de MAPA en ese paso
  choice   : Nat := 0          -- dos o mas ids de mapa
  pathOne  : Nat := 0          -- un solo PathNodeId: lo que el teorema pide
  pathMany : Nat := 0          -- mismo id de mapa pero ventanas distintas
  deriving Repr

def scanTCS (g : GPathM) (cap : Nat) (a : TCSAcc) : TCSAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for na in g.nodes.take cap do
    a := { a with tables := a.tables + 1 }
    match tableChain g na with
    | none => pure ()
    | some ch =>
      for u in ch do
        let here := ownersAt na.owners u.id.step
        let isSingle := here.all (fun w => w.id == u.id)
        let isPathOne := here.all (fun w => w == u)
        for v in ch do
          if u.id.step != v.id.step then
            a := { a with pairs := a.pairs + 1 }
            if isSingle then a := { a with single := a.single + 1 }
            else a := { a with choice := a.choice + 1 }
            if isPathOne then a := { a with pathOne := a.pathOne + 1 }
            else if isSingle then a := { a with pathMany := a.pathMany + 1 }
  return a

partial def walkTCS (g : GPathM) (fuel cap : Nat) (a : TCSAcc) : TCSAcc :=
  if fuel == 0 then a
  else
    let a := scanTCS g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkTCS (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaTCS (φ : Cnf) (cap : Nat) (a : TCSAcc) : TCSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkTCS g (stepCount φ).toNat cap a
  return a

def reportTCS (name : String) (a : TCSAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, tablas {a.tables}"
  IO.println s!"   pares de la cadena de la tabla: {a.pairs}"
  IO.println s!"     un solo id de MAPA en ese paso : {a.single}  ({pct a.single a.pairs})"
  IO.println s!"     dos o mas ids de mapa           : {a.choice}  ({pct a.choice a.pairs})"
  IO.println s!"   y lo que mem_owners_of_singleAt pide de verdad (un solo PathNodeId):"
  IO.println s!"     CERRADO                         : {a.pathOne}  ({pct a.pathOne a.pairs})"
  IO.println s!"     mismo id de mapa, otra ventana  : {a.pathMany}  ({pct a.pathMany a.pairs})"
  IO.println s!"   ({ms} ms)"

/-! **¿Cuanto cubre `realizes_pin_of_singleId`?** Cierra el caso en que la tabla de `x` NO tiene
eleccion en el paso del pin: todos sus owners alli llevan ya el pin. Esta sonda lo cuenta sobre los
pines que el lector se plantea de verdad. -/

structure PCAcc where
  formulas : Nat := 0
  states   : Nat := 0
  pins     : Nat := 0
  nodes    : Nat := 0          -- (pin, nodo que sobrevive)
  single   : Nat := 0          -- ... sin eleccion: cubierto por el teorema
  choice   : Nat := 0          -- ... con los dos valores: el residuo
  entries  : Nat := 0          -- (pin, nodo, owner) del residuo
  deriving Repr

def scanPinChoice (g : GPathM) (a : PCAcc) : PCAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  match ReaderExec.firstChoice g with
  | none => return a
  | some k =>
    for cand in ownersAt g.gowners k do
      let r := cand.id
      let h := filterAllAgg g [r]
      if isValid h then
        a := { a with pins := a.pins + 1 }
        for nx in h.nodes do
          match g.node? nx.id with
          | none => pure ()
          | some nx0 =>
            a := { a with nodes := a.nodes + 1 }
            let other := nx0.owners.filter (fun u => u.id.step == r.step && u.id != r)
            if other.isEmpty then a := { a with single := a.single + 1 }
            else
              a := { a with choice := a.choice + 1
                          , entries := a.entries + nx0.owners.length }
    return a

partial def walkPC (g : GPathM) (fuel : Nat) (a : PCAcc) : PCAcc :=
  if fuel == 0 then a
  else
    let a := scanPinChoice g a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkPC (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaPC (φ : Cnf) (a : PCAcc) : PCAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkPC g (stepCount φ).toNat a
  return a

def reportPC (name : String) (a : PCAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, pines validos {a.pins}"
  IO.println s!"   pares (pin, nodo superviviente): {a.nodes}"
  IO.println s!"     SIN eleccion -> cerrado por realizes_pin_of_singleId : {a.single}  ({pct a.single a.nodes})"
  IO.println s!"     con los dos valores -> el residuo                    : {a.choice}  ({pct a.choice a.nodes})"
  IO.println s!"   ({ms} ms)"

/-! **`anyoption`: la frase del lector, `OwnerChainedBuild.AnyOptionStep`, medida.**

Descenso colectivo dentro de la tabla de cada nodo `a`: se parte de una entrada `t` de la tabla de
`a` en la cima, y la tabla colectiva es `C = tabla(a) ∩ tabla(t) ∩ …`. En cada paso `lo` se mira
**cada** opción `u` de `C` en el paso `lo - 1` y se comprueba si `C ∩ tabla(u)` sigue con entrada en
todos los pasos de abajo. Se cuenta si valen todas (la versión «para toda u»), solo alguna («existe
una u») o ninguna; y el descenso sigue por la primera que vale. Se separa el caso de dos padres de
`sel lo` y el de ventana libre (`lo - 3` por encima de la frontera del lector). -/

structure AOAcc where
  formulas  : Nat := 0
  states    : Nat := 0
  descents  : Nat := 0
  seedBad   : Nat := 0
  reached0  : Nat := 0
  steps     : Nat := 0
  allOk     : Nat := 0
  someOnly  : Nat := 0
  noneOk    : Nat := 0
  options   : Nat := 0
  optOk     : Nat := 0
  twoPar    : Nat := 0
  twoParAll : Nat := 0
  freeWin   : Nat := 0
  freeWinAll : Nat := 0
  firstSome : String := ""
  firstNone : String := ""
  deriving Repr

def tableOfAO (g : GPathM) (x : PathNodeId) : List PathNodeId :=
  match g.node? x with
  | some n => n.owners
  | none => []

def collectiveOk (C : List PathNodeId) (lo : Int) : Bool :=
  (List.range lo.toNat).all (fun i => C.any (fun r => r.id.step == (i : Int)))

partial def descendAO (g : GPathM) (label : String) (aStep : Int) (m : Int)
    (C : List PathNodeId) (selLo : PathNodeId) (lo : Int) (a : AOAcc) : AOAcc :=
  if lo ≤ 0 then { a with reached0 := a.reached0 + 1 }
  else
    let opts := C.filter (fun u => u.id.step == lo - 1)
    let res := opts.map (fun u =>
      let Cu := C.filter (fun r => (tableOfAO g u).contains r)
      (u, Cu, collectiveOk Cu (lo - 1)))
    let nOk := (res.filter (fun x => x.2.2)).length
    let twoP := match g.node? selLo with
      | some n => distinctBy (fun (p : PathNodeId) => p) n.parents ≥ 2
      | none => false
    let free := lo - 3 ≥ m
    let allV := nOk == res.length && res.length > 0
    let where_ := s!"{label} a@{aStep} lo={lo} frontera={m} opciones={res.length} validas={nOk} dosPadres={twoP}"
    let a := { a with steps := a.steps + 1, options := a.options + res.length, optOk := a.optOk + nOk
                    , allOk := a.allOk + (if allV then 1 else 0)
                    , someOnly := a.someOnly + (if !allV && nOk > 0 then 1 else 0)
                    , noneOk := a.noneOk + (if nOk == 0 then 1 else 0)
                    , twoPar := a.twoPar + (if twoP then 1 else 0)
                    , twoParAll := a.twoParAll + (if twoP && allV then 1 else 0)
                    , freeWin := a.freeWin + (if free then 1 else 0)
                    , freeWinAll := a.freeWinAll + (if free && allV then 1 else 0)
                    , firstSome := if a.firstSome == "" && !allV && nOk > 0 then where_ else a.firstSome
                    , firstNone := if a.firstNone == "" && nOk == 0 then where_ else a.firstNone }
    match res.find? (fun x => x.2.2) with
    | none => a
    | some (u, Cu, _) => descendAO g label aStep m Cu u (lo - 1) a

def scanAO (label : String) (g : GPathM) (cap : Nat) (a : AOAcc) : AOAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  let m : Int := match ReaderExec.firstChoice g with
    | some k => k
    | none => g.current_step
  for na in g.nodes.take cap do
    for t in (ownersAt na.owners (g.current_step - 1)).take 3 do
      let C := na.owners.filter (fun r => (tableOfAO g t).contains r)
      a := { a with descents := a.descents + 1 }
      if collectiveOk C (g.current_step - 1) then
        a := descendAO g label na.id.id.step m C t (g.current_step - 1) a
      else
        a := { a with seedBad := a.seedBad + 1 }
  return a

partial def walkAO (label : String) (g : GPathM) (fuel cap : Nat) (a : AOAcc) : AOAcc :=
  if fuel == 0 then a
  else
    let a := scanAO label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkAO label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaAO (label : String) (φ : Cnf) (cap : Nat) (a : AOAcc) : AOAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkAO label g (stepCount φ).toNat cap a
  return a

def reportAO (name : String) (a : AOAcc) (ms : Nat) : IO Unit := do
  let pct (x y : Nat) : String :=
    if y == 0 then "-" else s!"{(x * 1000 / y) / 10}.{(x * 1000 / y) % 10}%"
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}, descensos {a.descents} (semilla mala {a.seedBad}), llegan al 0: {a.reached0}"
  IO.println s!"   pasos del descenso: {a.steps}   opciones {a.options}, validas {a.optOk} ({pct a.optOk a.options})"
  IO.println s!"     para toda u  : {a.allOk}  ({pct a.allOk a.steps})"
  IO.println s!"     solo alguna  : {a.someOnly}  ({pct a.someOnly a.steps})"
  IO.println s!"     ninguna      : {a.noneOk}  ({pct a.noneOk a.steps})"
  IO.println s!"   sel lo con dos padres : {a.twoPar}, de ellos para toda u: {a.twoParAll}"
  IO.println s!"   ventana libre (lo-3 ≥ frontera): {a.freeWin}, de ellos para toda u: {a.freeWinAll}"
  if a.firstSome != "" then IO.println s!"   primer 'solo alguna': {a.firstSome}"
  if a.firstNone != "" then IO.println s!"   primer 'ninguna'    : {a.firstNone}"
  IO.println s!"   ({ms} ms)"

/-! **`cliqueshare`: el invariante no local candidato.** Toda familia de nodos que se poseen dos a
dos tiene, en cada paso, una entrada común a todas sus tablas. Para dos nodos es `AggOk`
(`sharesEveryStep`); para `{a, sel lo, …, cima, u}` es `AnyOptionStep`. Se mide sobre ternas y sobre
cliques ávidas, en los estados del lector y en los de la línea de la máquina. -/

instance : Inhabited PathNodeId := ⟨{ id := ⟨0, 0⟩, parent_id := none }⟩

structure CSAcc where
  formulas : Nat := 0
  states   : Nat := 0
  triples  : Nat := 0
  tripBad  : Nat := 0
  cliques  : Nat := 0
  cliqBad  : Nat := 0
  maxSize  : Nat := 0
  firstBad : String := ""
  deriving Repr

def commonAll (g : GPathM) (S : List PathNodeId) : Bool :=
  (List.range g.current_step.toNat).all (fun i =>
    match S with
    | [] => true
    | x :: rest => (ownersAt (tableOfAO g x) (i : Int)).any (fun r =>
        rest.all (fun y => (tableOfAO g y).contains r)))

def scanCS (label : String) (g : GPathM) (cap : Nat) (a : CSAcc) : CSAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  let ns := (g.nodes.take cap).map (·.id)
  let arr := ns.toArray
  for i in [0:arr.size] do
    for j in [i+1:arr.size] do
      if mutuallyOwn g arr[i]! arr[j]! then
        for k in [j+1:arr.size] do
          if mutuallyOwn g arr[i]! arr[k]! && mutuallyOwn g arr[j]! arr[k]! then
            a := { a with triples := a.triples + 1 }
            if !commonAll g [arr[i]!, arr[j]!, arr[k]!] then
              a := { a with tripBad := a.tripBad + 1
                          , firstBad := if a.firstBad == "" then
                              s!"{label} terna {arr[i]!.id.step}/{arr[j]!.id.step}/{arr[k]!.id.step}"
                            else a.firstBad }
  for x in ns do
    let mut S : List PathNodeId := [x]
    for y in ns do
      if y != x && S.all (fun z => mutuallyOwn g y z) then
        S := S ++ [y]
        a := { a with cliques := a.cliques + 1, maxSize := max a.maxSize S.length }
        if !commonAll g S then
          a := { a with cliqBad := a.cliqBad + 1
                      , firstBad := if a.firstBad == "" then
                          s!"{label} clique de {S.length} desde {x.id.step}" else a.firstBad }
  return a

partial def walkCS (label : String) (g : GPathM) (fuel cap : Nat) (a : CSAcc) : CSAcc :=
  if fuel == 0 then a
  else
    let a := scanCS label g cap a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkCS label (filterAllAgg g [q.id]) (fuel - 1) cap a

def runFormulaCS (lineToo : Bool) (label : String) (φ : Cnf) (cap : Nat) (a : CSAcc) : CSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    -- el estado que la máquina aparca en la línea, tal cual, y la trayectoria del lector
    if lineToo && isValid kv.2 then a := scanCS s!"{label} linea" kv.2 cap a
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := walkCS label g (stepCount φ).toNat cap a
  return a

def reportCS (name : String) (a : CSAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}"
  IO.println s!"   formulas {a.formulas}, estados {a.states}"
  IO.println s!"   ternas que se poseen dos a dos : {a.triples}, sin entrada comun en algun paso: {a.tripBad}"
  IO.println s!"   cliques avidas (cada prefijo)  : {a.cliques}, sin entrada comun: {a.cliqBad}  (tamaño max {a.maxSize})"
  if a.firstBad != "" then IO.println s!"   primero: {a.firstBad}"
  IO.println s!"   ({ms} ms)"

/-! **`chainshare`: el candidato de cadenas.** Para un nodo `a` y una cadena parcial `sel lo … hi`
enlazada por padres, poseída por pares y poseída mutuamente con `a`: en cada paso `i < lo` hay una
entrada común a la tabla de `a` y a las de toda la cadena. Se recorren por DFS, con presupuesto, todas
las cadenas que bajan desde cada entrada de la tabla de `a`; `hi` es cualquiera, y se separa `hi` en la
cima (lo que usa el descenso). -/

structure CHAcc where
  formulas : Nat := 0
  states   : Nat := 0
  chains   : Nat := 0
  bad      : Nat := 0
  topCh    : Nat := 0
  topBad   : Nat := 0
  cut      : Nat := 0
  firstBad : String := ""
  deriving Repr

/-- La tabla colectiva de `a` y la cadena tiene entrada en todos los pasos `< lo`. -/
def chainCommonBelow (g : GPathM) (a : PathNodeId) (P : List PathNodeId) (lo : Int) : Bool :=
  (List.range lo.toNat).all (fun i =>
    (ownersAt (tableOfAO g a) (i : Int)).any (fun r => P.all (fun y => (tableOfAO g y).contains r)))

partial def dfsChains (g : GPathM) (label : String) (a : PathNodeId) (P : List PathNodeId)
    (isTop : Bool) (acc : CHAcc × Nat) : CHAcc × Nat :=
  let (c, budget) := acc
  if budget == 0 then ({ c with cut := c.cut + 1 }, 0)
  else
    match P with
    | [] => (c, budget)
    | low :: _ =>
      let lo := low.id.step
      let ok := chainCommonBelow g a P lo
      let c := { c with chains := c.chains + 1, bad := c.bad + (if ok then 0 else 1)
                      , topCh := c.topCh + (if isTop then 1 else 0)
                      , topBad := c.topBad + (if isTop && !ok then 1 else 0)
                      , firstBad := if c.firstBad == "" && !ok then
                          s!"{label} a@{a.id.step} cadena {P.map (·.id.step)}" else c.firstBad }
      let ps := match g.node? low with
        | some n => n.parents.filter (fun p => mutuallyOwn g p a && P.all (fun y => mutuallyOwn g p y))
        | none => []
      ps.foldl (fun acc p => dfsChains g label a (p :: P) isTop acc) (c, budget - 1)

def scanCH (label : String) (g : GPathM) (cap budget : Nat) (c : CHAcc) : CHAcc := Id.run do
  let mut c := { c with states := c.states + 1 }
  for na in g.nodes.take cap do
    let a := na.id
    for x in na.owners do
      if x.id.step ≥ 0 && x.id.step < g.current_step && mutuallyOwn g x a then
        let (c', _) := dfsChains g label a [x] (x.id.step == g.current_step - 1) (c, budget)
        c := c'
  return c

partial def walkCH (label : String) (g : GPathM) (fuel cap budget : Nat) (c : CHAcc) : CHAcc :=
  if fuel == 0 then c
  else
    let c := scanCH label g cap budget c
    match ReaderExec.firstChoice g with
    | none => c
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => c
      | some q => walkCH label (filterAllAgg g [q.id]) (fuel - 1) cap budget c

def runFormulaCH (lineToo : Bool) (label : String) (φ : Cnf) (cap budget : Nat) (c : CHAcc) :
    CHAcc := Id.run do
  let mut c := { c with formulas := c.formulas + 1 }
  for kv in pureRunW φ do
    if lineToo && isValid kv.2 then c := scanCH s!"{label} linea" kv.2 cap budget c
    let g := filterAllAgg kv.2 []
    if isValid g then
      c := walkCH label g (stepCount φ).toNat cap budget c
  return c

def reportCH (name : String) (c : CHAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}"
  IO.println s!"   formulas {c.formulas}, estados {c.states}, cadenas {c.chains} (recortes de presupuesto {c.cut})"
  IO.println s!"   sin entrada comun por debajo: {c.bad}"
  IO.println s!"   desde la cima: {c.topCh}, sin entrada comun: {c.topBad}"
  if c.firstBad != "" then IO.println s!"   primero: {c.firstBad}"
  IO.println s!"   ({ms} ms)"

/-! **`upextend`: ¿el `up` prolonga las cadenas buenas desde la cima?** En cada envío de la máquina,
`P` es el estado revisado que el `up` recibe y `U = addNode P d`. Para cada cadena buena de `P` desde
su cima (anfitrión `a`, enlazada por padres, poseída por pares, con entrada común por debajo), se
mira cada hijo `v` de la cima en la fila nueva: si `v` se posee mutuamente con `a` y con la cadena
en `U`, y si la cadena alargada sigue con entrada común por debajo. -/

structure UEAcc where
  formulas : Nat := 0
  sends    : Nat := 0
  chains   : Nat := 0
  good     : Nat := 0
  noSon    : Nat := 0
  someExt  : Nat := 0
  allExt   : Nat := 0
  sons     : Nat := 0
  sonsOk   : Nat := 0
  cut      : Nat := 0
  firstBad : String := ""
  deriving Repr

def extendsUp (U : GPathM) (a : PathNodeId) (P : List PathNodeId) (lo : Int) (v : PathNodeId) : Bool :=
  mutuallyOwn U v a && P.all (fun y => mutuallyOwn U v y) && chainCommonBelow U a (P ++ [v]) lo

partial def dfsUp (Pst U : GPathM) (label : String) (a : PathNodeId) (top : PathNodeId)
    (P : List PathNodeId) (acc : UEAcc × Nat) : UEAcc × Nat :=
  let (c, budget) := acc
  if budget == 0 then ({ c with cut := c.cut + 1 }, 0)
  else
    match P with
    | [] => (c, budget)
    | low :: _ =>
      let lo := low.id.step
      let c := { c with chains := c.chains + 1 }
      let c := if chainCommonBelow Pst a P lo then
          let sons := (U.nodes.filter (fun m => m.id.id.step == Pst.current_step && m.parents.contains top)).map (·.id)
          let oks := sons.filter (fun v => extendsUp U a P lo v)
          { c with good := c.good + 1, sons := c.sons + sons.length, sonsOk := c.sonsOk + oks.length
                 , noSon := c.noSon + (if sons.isEmpty then 1 else 0)
                 , someExt := c.someExt + (if oks.isEmpty then 0 else 1)
                 , allExt := c.allExt + (if !sons.isEmpty && oks.length == sons.length then 1 else 0)
                 , firstBad := if c.firstBad == "" && oks.length != sons.length then
                     s!"{label} a@{a.id.step} cadena {P.map (·.id.step)} hijos {sons.length} validos {oks.length}"
                   else c.firstBad }
        else c
      let ps := match Pst.node? low with
        | some n => n.parents.filter (fun p => mutuallyOwn Pst p a && P.all (fun y => mutuallyOwn Pst p y))
        | none => []
      ps.foldl (fun acc p => dfsUp Pst U label a top (p :: P) acc) (c, budget - 1)

def measureSend (label : String) (Pst U : GPathM) (cap budget : Nat) (c : UEAcc) : UEAcc := Id.run do
  let mut c := { c with sends := c.sends + 1 }
  for na in Pst.nodes.take cap do
    let a := na.id
    for t in ownersAt na.owners (Pst.current_step - 1) do
      if mutuallyOwn Pst t a then
        let (c', _) := dfsUp Pst U label a t [t] (c, budget)
        c := c'
  return c

def runFormulaUE (label : String) (φ : Cnf) (cap budget : Nat) (c : UEAcc) : UEAcc := Id.run do
  let mut c := { c with formulas := c.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let Pst := filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)
        if isValid Pst then
          c := measureSend s!"{label} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" Pst
            (addNode Pst d "") cap budget c
    line := pureAdvanceW φ line
  return c

def reportUE (name : String) (c : UEAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}"
  IO.println s!"   formulas {c.formulas}, envios validos {c.sends}, cadenas desde la cima {c.chains} (recortes {c.cut})"
  IO.println s!"   buenas (entrada comun por debajo): {c.good}"
  IO.println s!"     la cima no tiene hijo en la fila : {c.noSon}"
  IO.println s!"     algun hijo la prolonga           : {c.someExt}"
  IO.println s!"     TODOS los hijos la prolongan     : {c.allExt}"
  IO.println s!"   hijos probados {c.sons}, validos {c.sonsOk}"
  if c.firstBad != "" then IO.println s!"   primero con algun hijo que no: {c.firstBad}"
  IO.println s!"   ({ms} ms)"

/-! **`topgoodops`: `TopGood` estado a estado del envío.** Se cuentan las cadenas desde la cima (con
anfitrión, enlazadas, poseídas por pares) y cuántas no tienen entrada común por debajo, en cada clase
de estado: la línea (tras el `doJoin`), la revisión base (`review`), el review agresivo completo
(`filterAllAgg`, lo que el `up` recibe), el `up`, y los estados del lector. Los filtros no tocan
tablas, así que no cambian `TopGood`. Solo los estados REVISADOS cuentan como fallo de verdad. -/

structure TGCell where
  states : Nat := 0
  chains : Nat := 0
  bad    : Nat := 0
  statesBad : Nat := 0
  first  : String := ""
  deriving Repr

partial def dfsTop (g : GPathM) (a : PathNodeId) (P : List PathNodeId) (acc : Nat × Nat × Nat) :
    Nat × Nat × Nat :=
  let (chains, bad, budget) := acc
  if budget == 0 then (chains, bad, 0)
  else
    match P with
    | [] => acc
    | low :: _ =>
      let ok := chainCommonBelow g a P low.id.step
      let ps := match g.node? low with
        | some n => n.parents.filter (fun p => mutuallyOwn g p a && P.all (fun y => mutuallyOwn g p y))
        | none => []
      ps.foldl (fun acc p => dfsTop g a (p :: P) acc)
        (chains + 1, bad + (if ok then 0 else 1), budget - 1)

def measureTG (label : String) (g : GPathM) (cap budget : Nat) (c : TGCell) : TGCell := Id.run do
  if !isValid g then return c
  let mut ch := 0
  let mut bd := 0
  for na in g.nodes.take cap do
    for t in ownersAt na.owners (g.current_step - 1) do
      if mutuallyOwn g t na.id then
        let (c1, b1, _) := dfsTop g na.id [t] (0, 0, budget)
        ch := ch + c1
        bd := bd + b1
  return { states := c.states + 1, chains := c.chains + ch, bad := c.bad + bd
         , statesBad := c.statesBad + (if bd > 0 then 1 else 0)
         , first := if c.first == "" && bd > 0 then label else c.first }

structure TGAcc where
  formulas : Nat := 0
  line     : TGCell := {}
  base     : TGCell := {}
  agg      : TGCell := {}
  up       : TGCell := {}
  reader   : TGCell := {}
  deriving Repr

partial def walkTG (label : String) (g : GPathM) (fuel cap budget : Nat) (c : TGCell) : TGCell :=
  if fuel == 0 then c
  else
    let c := measureTG label g cap budget c
    match ReaderExec.firstChoice g with
    | none => c
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => c
      | some q => walkTG label (filterAllAgg g [q.id]) (fuel - 1) cap budget c

def runFormulaTG (label : String) (φ : Cnf) (cap budget : Nat) (a : TGAcc) : TGAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      let lab := s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩"
      a := { a with line := measureTG s!"{lab} linea" kv.2 cap budget a.line }
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        let B := review F
        a := { a with base := measureTG s!"{lab}→⟨{d.step},{d.index}⟩ review" B cap budget a.base }
        let R := AggressiveReview.reviewAgg F
        if isValid R then
          a := { a with agg := measureTG s!"{lab}→⟨{d.step},{d.index}⟩ agg" R cap budget a.agg
                      , up := measureTG s!"{lab}→⟨{d.step},{d.index}⟩ up" (addNode R d "") cap budget a.up }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with reader := walkTG s!"{label} lector" g (stepCount φ).toNat cap budget a.reader }
  return a

def reportTG (name : String) (a : TGAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  let row (lbl : String) (c : TGCell) : IO Unit := do
    IO.println s!"   {lbl}: estados {c.states} (con fallo {c.statesBad}), cadenas {c.chains}, sin entrada comun {c.bad}"
    if c.first != "" then IO.println s!"      primero: {c.first}"
  row "linea (tras doJoin)     " a.line
  row "revision base (review)  " a.base
  row "review agresivo  [REV]  " a.agg
  row "up                      " a.up
  row "lector           [REV]  " a.reader
  IO.println s!"   ({ms} ms)"

/-! **`joinmix`: ¿hay cadenas del `doJoin` que no son de ningún lado?** En cada unión real de la
línea, `J = doJoin A B`: para cada cadena desde la cima de `J` (anfitrión, enlazada, poseída por
pares) se mira si lo es también en `A` o en `B` con sus propias tablas y padres. Las que no, son
**mezcladas**; se cuentan, y cuántas de ellas son malas. -/

structure JMAcc where
  formulas : Nat := 0
  joins    : Nat := 0
  chains   : Nat := 0
  inA      : Nat := 0
  inB      : Nat := 0
  mixed    : Nat := 0
  mixedBad : Nat := 0
  bad      : Nat := 0
  first    : String := ""
  deriving Repr

/-- `P` (de abajo a la cima) es cadena con anfitrión `a` en `g`, con las tablas y padres de `g`. -/
def chainIn (g : GPathM) (a : PathNodeId) (P : List PathNodeId) : Bool :=
  (g.node? a).isSome && P.all (fun x => (g.node? x).isSome && mutuallyOwn g x a) &&
  P.all (fun x => P.all (fun y => x == y || mutuallyOwn g x y)) &&
  (List.range (P.length - 1)).all (fun k =>
    match g.node? (P.getD (k + 1) a) with
    | some n => n.parents.contains (P.getD k a)
    | none => false)

partial def dfsJM (J A B : GPathM) (label : String) (a : PathNodeId) (P : List PathNodeId)
    (acc : JMAcc × Nat) : JMAcc × Nat :=
  let (c, budget) := acc
  if budget == 0 then (c, 0)
  else
    match P with
    | [] => acc
    | low :: _ =>
      let ok := chainCommonBelow J a P low.id.step
      let ia := chainIn A a P
      let ib := chainIn B a P
      let mix := !ia && !ib
      let c := { c with chains := c.chains + 1, inA := c.inA + (if ia then 1 else 0)
                      , inB := c.inB + (if ib then 1 else 0), mixed := c.mixed + (if mix then 1 else 0)
                      , mixedBad := c.mixedBad + (if mix && !ok then 1 else 0)
                      , bad := c.bad + (if ok then 0 else 1)
                      , first := if c.first == "" && mix then
                          s!"{label} a@{a.id.step} cadena {P.map (·.id.step)} buena={ok}" else c.first }
      let ps := match J.node? low with
        | some n => n.parents.filter (fun p => mutuallyOwn J p a && P.all (fun y => mutuallyOwn J p y))
        | none => []
      ps.foldl (fun acc p => dfsJM J A B label a (p :: P) acc) (c, budget - 1)

def measureJM (label : String) (A B : GPathM) (cap budget : Nat) (c : JMAcc) : JMAcc := Id.run do
  let J := doJoin A B
  if !(okJoin A B) || !isValid J then return c
  let mut c := { c with joins := c.joins + 1 }
  for na in J.nodes.take cap do
    for t in ownersAt na.owners (J.current_step - 1) do
      if mutuallyOwn J t na.id then
        let (c', _) := dfsJM J A B label na.id [t] (c, budget)
        c := c'
  return c

def runFormulaJM (label : String) (φ : Cnf) (cap budget : Nat) (c : JMAcc) : JMAcc := Id.run do
  let mut c := { c with formulas := c.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let h := upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
        if isValid h then
          match next.find? (fun e => e.1 == d) with
          | some (_, existing) =>
            c := measureJM s!"{label} paso {step} →⟨{d.step},{d.index}⟩" existing h cap budget c
            next := next.map (fun e => if e.1 == d then (d, doJoin existing h) else e)
          | none => next := next ++ [(d, h)]
    line := next
  return c

def reportJM (name : String) (c : JMAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({c.formulas} formulas)"
  IO.println s!"   uniones {c.joins}, cadenas desde la cima {c.chains}, malas {c.bad}"
  IO.println s!"     cadena de A: {c.inA}   cadena de B: {c.inB}"
  IO.println s!"     MEZCLADAS (de ningun lado): {c.mixed}, malas entre ellas: {c.mixedBad}"
  if c.first != "" then IO.println s!"   primera mezclada: {c.first}"
  IO.println s!"   ({ms} ms)"

/-! **`reviewops`: `TopGood` tras cada sub-paso del review.** Para cada envío, desde el estado filtrado
`F`, se rehace `reviewAgg` a mano: vueltas de `review` (cada una `cleanInvalid`, pasada de padres,
pasada de hijos) hasta el punto fijo, y luego el barrido agresivo, mientras quite algo. Se mide
`TopGood` tras cada sub-paso (solo estados válidos) y también en `F` mismo. -/

structure ROAcc where
  formulas : Nat := 0
  filt   : TGCell := {}
  clean  : TGCell := {}
  par    : TGCell := {}
  sons   : TGCell := {}
  sweep  : TGCell := {}
  final  : TGCell := {}
  deriving Repr

def reviewInstr (lab : String) (F : GPathM) (cap budget : Nat) (a : ROAcc) : ROAcc := Id.run do
  let mut a := { a with filt := measureTG s!"{lab} filtrado" F cap budget a.filt }
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    -- review hasta el punto fijo
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g1 := cleanInvalid g
        a := { a with clean := measureTG s!"{lab} cleanInvalid" g1 cap budget a.clean }
        let g2 := reviewParents g1
        a := { a with par := measureTG s!"{lab} padres" g2 cap budget a.par }
        let g3 := reviewSons g2
        a := { a with sons := measureTG s!"{lab} hijos" g3 cap budget a.sons }
        if GPathM.measure g3 < GPathM.measure g then g := g3 else
          g := g3
          fuel := 0
    if !isValid g then outer := 0
    else
      let g2 := AggressiveReview.aggSweep g
      a := { a with sweep := measureTG s!"{lab} barrido" g2 cap budget a.sweep }
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  a := { a with final := measureTG s!"{lab} final" g cap budget a.final }
  return a

def runFormulaRO (label : String) (φ : Cnf) (cap budget : Nat) (a : ROAcc) : ROAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewInstr s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

def reportRO (name : String) (a : ROAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  let row (lbl : String) (c : TGCell) : IO Unit := do
    IO.println s!"   {lbl}: estados {c.states} (con fallo {c.statesBad}), cadenas {c.chains}, sin entrada comun {c.bad}"
    if c.first != "" then IO.println s!"      primero: {c.first}"
  row "filtrado (entrada)  " a.filt
  row "tras cleanInvalid   " a.clean
  row "tras pasada padres  " a.par
  row "tras pasada hijos   " a.sons
  row "tras barrido agres. " a.sweep
  row "final (reviewAgg)   " a.final
  IO.println s!"   ({ms} ms)"

/-! **`reviewnodes`: `TopGood` nodo a nodo dentro del review.** Como `reviewops`, pero midiendo tras
cada operación de un nodo: un paso de `cleanInvalidGo`, cada `reviewNode` de las pasadas de padres e
hijos, y cada `aggNode` del barrido. -/

structure RNAcc where
  formulas : Nat := 0
  clean : TGCell := {}
  par   : TGCell := {}
  sons  : TGCell := {}
  agg   : TGCell := {}
  deriving Repr

def instrSteps (lab : String) (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int)
    (cap budget : Nat) (c0 : TGCell) : GPathM × TGCell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      g := reviewNode g nb id
      c := measureTG s!"{lab} nodo@{id.id.step}" g cap budget c
  return (g, c)

def reviewNodesInstr (lab : String) (F : GPathM) (cap budget : Nat) (a : RNAcc) : RNAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        -- cleanInvalid, nodo a nodo
        let mut h := g
        for id in g.nodes.map (·.id) do
          h := cleanInvalidGo h [id]
          a := { a with clean := measureTG s!"{lab} clean@{id.id.step}" h cap budget a.clean }
        let (h2, cp) := instrSteps lab h (·.parents) (intRange 1 (h.current_step - 1)) cap budget a.par
        a := { a with par := cp }
        let (h3, cs) := instrSteps lab h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse cap budget a.sons
        a := { a with sons := cs }
        g := h3
        if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g0 := g
      let mut h := g
      for k in (intRange 0 (g.current_step - 1)).reverse do
        for id in (h.line k).map (·.id) do
          h := AggressiveReview.aggNode h id
          a := { a with agg := measureTG s!"{lab} agg@{id.id.step}" h cap budget a.agg }
      if GPathM.measure h < GPathM.measure g0 then g := h else outer := 0
  return a

def runFormulaRN (label : String) (φ : Cnf) (cap budget : Nat) (a : RNAcc) : RNAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewNodesInstr s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

def reportRN (name : String) (a : RNAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  let row (lbl : String) (c : TGCell) : IO Unit := do
    IO.println s!"   {lbl}: estados {c.states} (con fallo {c.statesBad}), cadenas {c.chains}, sin entrada comun {c.bad}"
    if c.first != "" then IO.println s!"      primero: {c.first}"
  row "cleanInvalid, por nodo " a.clean
  row "pasada padres, por nodo" a.par
  row "pasada hijos, por nodo " a.sons
  row "barrido, por nodo      " a.agg
  IO.println s!"   ({ms} ms)"

/-! **`nohost`: `TopGood` SIN anfitrión.** Toda cadena desde la cima, enlazada por padres y poseída por
pares, tiene en cada paso de abajo una entrada común a las tablas de sus miembros. Se mide con las
mismas clases de estado que `topgoodops` (`nohostops`) y nodo a nodo dentro del review
(`nohostnodes`). -/

def commonBelowNH (g : GPathM) (P : List PathNodeId) (lo : Int) : Bool :=
  (List.range lo.toNat).all (fun i =>
    match P with
    | [] => true
    | x :: rest => (ownersAt (tableOfAO g x) (i : Int)).any (fun r =>
        rest.all (fun y => (tableOfAO g y).contains r)))

partial def dfsNH (g : GPathM) (P : List PathNodeId) (acc : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (chains, bad, budget) := acc
  if budget == 0 then (chains, bad, 0)
  else
    match P with
    | [] => acc
    | low :: _ =>
      let ok := commonBelowNH g P low.id.step
      let ps := match g.node? low with
        | some n => n.parents.filter (fun p => P.all (fun y => mutuallyOwn g p y))
        | none => []
      ps.foldl (fun acc p => dfsNH g (p :: P) acc)
        (chains + 1, bad + (if ok then 0 else 1), budget - 1)

def measureNH (label : String) (g : GPathM) (_cap budget : Nat) (c : TGCell) : TGCell := Id.run do
  if !isValid g then return c
  let mut ch := 0
  let mut bd := 0
  for t in (g.line (g.current_step - 1)).map (·.id) do
    let (c1, b1, _) := dfsNH g [t] (0, 0, budget)
    ch := ch + c1
    bd := bd + b1
  return { states := c.states + 1, chains := c.chains + ch, bad := c.bad + bd
         , statesBad := c.statesBad + (if bd > 0 then 1 else 0)
         , first := if c.first == "" && bd > 0 then label else c.first }

partial def walkNHo (label : String) (g : GPathM) (fuel cap budget : Nat) (c : TGCell) : TGCell :=
  if fuel == 0 then c
  else
    let c := measureNH label g cap budget c
    match ReaderExec.firstChoice g with
    | none => c
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => c
      | some q => walkNHo label (filterAllAgg g [q.id]) (fuel - 1) cap budget c

def runFormulaNHo (label : String) (φ : Cnf) (cap budget : Nat) (a : TGAcc) : TGAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      let lab := s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩"
      a := { a with line := measureNH s!"{lab} linea" kv.2 cap budget a.line }
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        let B := review F
        a := { a with base := measureNH s!"{lab}→⟨{d.step},{d.index}⟩ review" B cap budget a.base }
        let R := AggressiveReview.reviewAgg F
        if isValid R then
          a := { a with agg := measureNH s!"{lab}→⟨{d.step},{d.index}⟩ agg" R cap budget a.agg
                      , up := measureNH s!"{lab}→⟨{d.step},{d.index}⟩ up" (addNode R d "") cap budget a.up }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with reader := walkNHo s!"{label} lector" g (stepCount φ).toNat cap budget a.reader }
  return a

def instrStepsNH (lab : String) (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int)
    (cap budget : Nat) (c0 : TGCell) : GPathM × TGCell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      g := reviewNode g nb id
      c := measureNH s!"{lab} nodo@{id.id.step}" g cap budget c
  return (g, c)

def reviewNodesNH (lab : String) (F : GPathM) (cap budget : Nat) (a : RNAcc) : RNAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        -- cleanInvalid, nodo a nodo
        let mut h := g
        for id in g.nodes.map (·.id) do
          h := cleanInvalidGo h [id]
          a := { a with clean := measureNH s!"{lab} clean@{id.id.step}" h cap budget a.clean }
        let (h2, cp) := instrStepsNH lab h (·.parents) (intRange 1 (h.current_step - 1)) cap budget a.par
        a := { a with par := cp }
        let (h3, cs) := instrStepsNH lab h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse cap budget a.sons
        a := { a with sons := cs }
        g := h3
        if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g0 := g
      let mut h := g
      for k in (intRange 0 (g.current_step - 1)).reverse do
        for id in (h.line k).map (·.id) do
          h := AggressiveReview.aggNode h id
          a := { a with agg := measureNH s!"{lab} agg@{id.id.step}" h cap budget a.agg }
      if GPathM.measure h < GPathM.measure g0 then g := h else outer := 0
  return a

def runFormulaNHn (label : String) (φ : Cnf) (cap budget : Nat) (a : RNAcc) : RNAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewNodesNH s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

/-! **`segments`: tramos sin anfitrión que NO arrancan en la cima.** Bajando: todo tramo enlazado y
poseído por pares, con extremo alto cualquiera, ¿tiene entrada común en cada paso por debajo? Y
subiendo: todo tramo que crece por hijos desde un nodo cualquiera, ¿la tiene en cada paso por
encima? Son las dos mitades de construir la cadena DESDE `a`. -/

def commonAboveNH (g : GPathM) (P : List PathNodeId) (hi : Int) : Bool :=
  (List.range (g.current_step - 1 - hi).toNat).all (fun k =>
    let i : Int := hi + 1 + k
    match P with
    | [] => true
    | x :: rest => (ownersAt (tableOfAO g x) i).any (fun r =>
        rest.all (fun y => (tableOfAO g y).contains r)))

partial def dfsUpNH (g : GPathM) (P : List PathNodeId) (acc : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (chains, bad, budget) := acc
  if budget == 0 then (chains, bad, 0)
  else
    match P with
    | [] => acc
    | high :: _ =>
      let ok := commonAboveNH g P high.id.step
      let ss := match g.node? high with
        | some n => n.sons.filter (fun q => P.all (fun y => mutuallyOwn g q y))
        | none => []
      ss.foldl (fun acc q => dfsUpNH g (q :: P) acc)
        (chains + 1, bad + (if ok then 0 else 1), budget - 1)

structure SGAcc where
  formulas : Nat := 0
  states   : Nat := 0
  down     : Nat := 0
  downBad  : Nat := 0
  up       : Nat := 0
  upBad    : Nat := 0
  firstDown : String := ""
  firstUp   : String := ""
  deriving Repr

def scanSG (label : String) (g : GPathM) (cap budget : Nat) (a : SGAcc) : SGAcc := Id.run do
  let mut a := { a with states := a.states + 1 }
  for n in g.nodes.take cap do
    let (c1, b1, _) := dfsNH g [n.id] (0, 0, budget)
    let (c2, b2, _) := dfsUpNH g [n.id] (0, 0, budget)
    a := { a with down := a.down + c1, downBad := a.downBad + b1, up := a.up + c2, upBad := a.upBad + b2
                , firstDown := if a.firstDown == "" && b1 > 0 then s!"{label} desde @{n.id.id.step}" else a.firstDown
                , firstUp := if a.firstUp == "" && b2 > 0 then s!"{label} desde @{n.id.id.step}" else a.firstUp }
  return a

partial def walkSG (label : String) (g : GPathM) (fuel cap budget : Nat) (a : SGAcc) : SGAcc :=
  if fuel == 0 then a
  else
    let a := scanSG label g cap budget a
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkSG label (filterAllAgg g [q.id]) (fuel - 1) cap budget a

def runFormulaSG (label : String) (φ : Cnf) (cap budget : Nat) (a : SGAcc) : SGAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    if isValid kv.2 then a := scanSG s!"{label} linea" kv.2 cap budget a
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkSG s!"{label} lector" g (stepCount φ).toNat cap budget a
  return a

def reportSG (name : String) (a : SGAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.states} estados)"
  IO.println s!"   bajando  (extremo alto cualquiera): tramos {a.down}, sin entrada comun debajo {a.downBad}"
  if a.firstDown != "" then IO.println s!"      primero: {a.firstDown}"
  IO.println s!"   subiendo (por hijos)              : tramos {a.up}, sin entrada comun encima {a.upBad}"
  if a.firstUp != "" then IO.println s!"      primero: {a.firstUp}"
  IO.println s!"   ({ms} ms)"

/-- `SegGood` en un estado: tramos desde cada nodo, bajando y subiendo, sin anfitrión. -/
def measureSEG (label : String) (g : GPathM) (cap budget : Nat) (c : TGCell) : TGCell := Id.run do
  if !isValid g then return c
  let mut ch := 0
  let mut bd := 0
  for n in g.nodes.take cap do
    let (c1, b1, _) := dfsNH g [n.id] (0, 0, budget)
    let (c2, b2, _) := dfsUpNH g [n.id] (0, 0, budget)
    ch := ch + c1 + c2
    bd := bd + b1 + b2
  return { states := c.states + 1, chains := c.chains + ch, bad := c.bad + bd
         , statesBad := c.statesBad + (if bd > 0 then 1 else 0)
         , first := if c.first == "" && bd > 0 then label else c.first }

partial def walkSGo (label : String) (g : GPathM) (fuel cap budget : Nat) (c : TGCell) : TGCell :=
  if fuel == 0 then c
  else
    let c := measureSEG label g cap budget c
    match ReaderExec.firstChoice g with
    | none => c
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => c
      | some q => walkSGo label (filterAllAgg g [q.id]) (fuel - 1) cap budget c

def runFormulaSGo (label : String) (φ : Cnf) (cap budget : Nat) (a : TGAcc) : TGAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      let lab := s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩"
      a := { a with line := measureSEG s!"{lab} linea" kv.2 cap budget a.line }
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        let B := review F
        a := { a with base := measureSEG s!"{lab}→⟨{d.step},{d.index}⟩ review" B cap budget a.base }
        let R := AggressiveReview.reviewAgg F
        if isValid R then
          a := { a with agg := measureSEG s!"{lab}→⟨{d.step},{d.index}⟩ agg" R cap budget a.agg
                      , up := measureSEG s!"{lab}→⟨{d.step},{d.index}⟩ up" (addNode R d "") cap budget a.up }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with reader := walkSGo s!"{label} lector" g (stepCount φ).toNat cap budget a.reader }
  return a

def instrStepsSG (lab : String) (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int)
    (cap budget : Nat) (c0 : TGCell) : GPathM × TGCell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      g := reviewNode g nb id
      c := measureSEG s!"{lab} nodo@{id.id.step}" g cap budget c
  return (g, c)

def reviewNodesSG (lab : String) (F : GPathM) (cap budget : Nat) (a : RNAcc) : RNAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        -- cleanInvalid, nodo a nodo
        let mut h := g
        for id in g.nodes.map (·.id) do
          h := cleanInvalidGo h [id]
          a := { a with clean := measureSEG s!"{lab} clean@{id.id.step}" h cap budget a.clean }
        let (h2, cp) := instrStepsSG lab h (·.parents) (intRange 1 (h.current_step - 1)) cap budget a.par
        a := { a with par := cp }
        let (h3, cs) := instrStepsSG lab h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse cap budget a.sons
        a := { a with sons := cs }
        g := h3
        if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g0 := g
      let mut h := g
      for k in (intRange 0 (g.current_step - 1)).reverse do
        for id in (h.line k).map (·.id) do
          h := AggressiveReview.aggNode h id
          a := { a with agg := measureSEG s!"{lab} agg@{id.id.step}" h cap budget a.agg }
      if GPathM.measure h < GPathM.measure g0 then g := h else outer := 0
  return a

def runFormulaSGn (label : String) (φ : Cnf) (cap budget : Nat) (a : RNAcc) : RNAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewNodesSG s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

/-! **`cleandiag`: qué pasa con los tramos que `cleanInvalid` rompe a medias.** Dentro de cada pasada
de `cleanInvalid` (nodo a nodo), se recogen los tramos (sin anfitrión, bajando y subiendo) que
quedan sin entrada común en algún estado intermedio, y al acabar la pasada se mira si siguen siendo
tramo —nodos vivos, enlazados, poseídos por pares— y, si siguen, si ya tienen entrada común. -/

partial def dfsNHc (g : GPathM) (P : List PathNodeId) (acc : List (List PathNodeId) × Nat) :
    List (List PathNodeId) × Nat :=
  let (bad, budget) := acc
  if budget == 0 then acc
  else
    match P with
    | [] => acc
    | low :: _ =>
      let bad := if commonBelowNH g P low.id.step then bad else P :: bad
      let ps := match g.node? low with
        | some n => n.parents.filter (fun p => P.all (fun y => mutuallyOwn g p y))
        | none => []
      ps.foldl (fun acc p => dfsNHc g (p :: P) acc) (bad, budget - 1)

partial def dfsUpNHc (g : GPathM) (P : List PathNodeId) (acc : List (List PathNodeId) × Nat) :
    List (List PathNodeId) × Nat :=
  let (bad, budget) := acc
  if budget == 0 then acc
  else
    match P with
    | [] => acc
    | high :: _ =>
      let bad := if commonAboveNH g P high.id.step then bad else P.reverse :: bad
      let ss := match g.node? high with
        | some n => n.sons.filter (fun q => P.all (fun y => mutuallyOwn g q y))
        | none => []
      ss.foldl (fun acc q => dfsUpNHc g (q :: P) acc) (bad, budget - 1)

/-- Tramo de abajo arriba: nodos vivos, enlazados por padres, poseídos por pares. -/
def isSegment (g : GPathM) (P : List PathNodeId) : Bool :=
  P.all (fun x => (g.node? x).isSome) &&
  P.all (fun x => P.all (fun y => x == y || mutuallyOwn g x y)) &&
  (List.range (P.length - 1)).all (fun k =>
    match P[k + 1]?, P[k]? with
    | some hi, some lo =>
      match g.node? hi with
      | some n => n.parents.contains lo
      | none => false
    | _, _ => false)

def segGoodOf (g : GPathM) (P : List PathNodeId) : Bool :=
  match P.head?, P.getLast? with
  | some lo, some hi => commonBelowNH g P lo.id.step && commonAboveNH g P.reverse hi.id.step
  | _, _ => true

structure CDAcc where
  formulas : Nat := 0
  passes   : Nat := 0
  passesBad : Nat := 0
  broken   : Nat := 0      -- tramos rotos a medias (distintos, por pasada)
  survive  : Nat := 0      -- siguen siendo tramo al final
  survGood : Nat := 0      -- ... y tienen entrada común al final
  die      : Nat := 0
  dieNode  : Nat := 0      -- ... porque muere algún nodo
  dieLink  : Nat := 0      -- ... nodos vivos pero se pierde un enlace o una posesión
  finalBad : Nat := 0      -- estados finales de la pasada con algún tramo malo
  firstSurv : String := ""
  deriving Repr

def diagClean (lab : String) (g : GPathM) (cap budget : Nat) (a : CDAcc) : CDAcc := Id.run do
  let mut a := { a with passes := a.passes + 1 }
  let mut h := g
  let mut broken : List (List PathNodeId) := []
  for id in g.nodes.map (·.id) do
    h := cleanInvalidGo h [id]
    if isValid h then
      for n in h.nodes.take cap do
        let (b1, _) := dfsNHc h [n.id] ([], budget)
        let (b2, _) := dfsUpNHc h [n.id] ([], budget)
        for P in b1 ++ b2 do
          if !broken.contains P then broken := P :: broken
  if !broken.isEmpty then a := { a with passesBad := a.passesBad + 1 }
  -- el final de la pasada
  if isValid h then
    let mut fb := false
    for n in h.nodes.take cap do
      let (b1, _) := dfsNHc h [n.id] ([], budget)
      let (b2, _) := dfsUpNHc h [n.id] ([], budget)
      if !(b1 ++ b2).isEmpty then fb := true
    if fb then a := { a with finalBad := a.finalBad + 1 }
  for P in broken do
    a := { a with broken := a.broken + 1 }
    if isValid h && isSegment h P then
      a := { a with survive := a.survive + 1
                  , survGood := a.survGood + (if segGoodOf h P then 1 else 0)
                  , firstSurv := if a.firstSurv == "" then s!"{lab} tramo {P.map (·.id.step)}" else a.firstSurv }
    else
      let allAlive := P.all (fun x => (h.node? x).isSome)
      a := { a with die := a.die + 1, dieNode := a.dieNode + (if allAlive then 0 else 1)
                  , dieLink := a.dieLink + (if allAlive then 1 else 0) }
  return a

def reviewDiag (lab : String) (F : GPathM) (cap budget : Nat) (a : CDAcc) : CDAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        a := diagClean lab g cap budget a
        let g3 := reviewSons (reviewParents (cleanInvalid g))
        g := g3
        if !(GPathM.measure g3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g2 := AggressiveReview.aggSweep g
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  return a

def runFormulaCD (label : String) (φ : Cnf) (cap budget : Nat) (a : CDAcc) : CDAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewDiag s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

def reportCD (name : String) (a : CDAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   pasadas de cleanInvalid {a.passes}, con algun tramo roto a medias {a.passesBad}"
  IO.println s!"   estados FINALES de pasada con algun tramo malo: {a.finalBad}"
  IO.println s!"   tramos rotos a medias: {a.broken}"
  IO.println s!"     siguen siendo tramo al final: {a.survive}  (con entrada comun al final: {a.survGood})"
  IO.println s!"     dejan de serlo             : {a.die}  (muere un nodo: {a.dieNode}; nodos vivos, cae enlace/posesion: {a.dieLink})"
  if a.firstSurv != "" then IO.println s!"   primero que sobrevive: {a.firstSurv}"
  IO.println s!"   ({ms} ms)"

/-! **`midinv`: las propiedades de forma en los estados intermedios del review.** (I1) en el paso de
justo abajo, owner es padre; (I2) simetría de tablas; (I3) toda entrada de una tabla, en rango, es
nodo. Se cuentan los estados que violan cada una, tras cada operación de nodo de cada pasada. -/

structure MICell where
  states : Nat := 0
  i1s : Nat := 0
  i1 : Nat := 0
  i2 : Nat := 0
  i3 : Nat := 0
  deriving Repr

def checkMI (g : GPathM) (c : MICell) : MICell := Id.run do
  if !isValid g then return c
  let mut b1 := false
  let mut b2 := false
  let mut b3 := false
  let mut b4 := false
  for n in g.nodes do
    for w in n.owners do
      if w.id.step ≥ 0 && w.id.step < g.current_step then
        match g.node? w with
        | none => b3 := true
        | some m =>
          if !m.owners.contains n.id then b2 := true
          if w.id.step + 1 == n.id.id.step && !n.parents.contains w then b1 := true
          if w.id.step == n.id.id.step + 1 && !n.sons.contains w then b4 := true
  return { states := c.states + 1, i1s := c.i1s + (if b4 then 1 else 0), i1 := c.i1 + (if b1 then 1 else 0)
         , i2 := c.i2 + (if b2 then 1 else 0), i3 := c.i3 + (if b3 then 1 else 0) }

structure MIAcc where
  formulas : Nat := 0
  filt  : MICell := {}
  clean : MICell := {}
  par   : MICell := {}
  sons  : MICell := {}
  agg   : MICell := {}
  deriving Repr

def instrStepsMI (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int) (c0 : MICell) :
    GPathM × MICell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      g := reviewNode g nb id
      c := checkMI g c
  return (g, c)

def reviewMI (F : GPathM) (a : MIAcc) : MIAcc := Id.run do
  let mut a := { a with filt := checkMI F a.filt }
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        let mut h := g
        for id in g.nodes.map (·.id) do
          h := cleanInvalidGo h [id]
          a := { a with clean := checkMI h a.clean }
        let (h2, cp) := instrStepsMI h (·.parents) (intRange 1 (h.current_step - 1)) a.par
        a := { a with par := cp }
        let (h3, cs) := instrStepsMI h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse a.sons
        a := { a with sons := cs }
        g := h3
        if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g0 := g
      let mut h := g
      for k in (intRange 0 (g.current_step - 1)).reverse do
        for id in (h.line k).map (·.id) do
          h := AggressiveReview.aggNode h id
          a := { a with agg := checkMI h a.agg }
      if GPathM.measure h < GPathM.measure g0 then g := h else outer := 0
  return a

def runFormulaMI (φ : Cnf) (a : MIAcc) : MIAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewMI F a
    line := pureAdvanceW φ line
  return a

def reportMI (name : String) (a : MIAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  let row (lbl : String) (c : MICell) : IO Unit :=
    IO.println s!"   {lbl}: estados {c.states}; violan (I1) owner-debajo=padre {c.i1}, (I2) simetria {c.i2}, (I3) owner es nodo {c.i3}, (I1-hijos) owner-encima=hijo {c.i1s}"
  row "filtrado (entrada)     " a.filt
  row "cleanInvalid, por nodo " a.clean
  row "pasada padres, por nodo" a.par
  row "pasada hijos, por nodo " a.sons
  row "barrido, por nodo      " a.agg
  IO.println s!"   ({ms} ms)"

/-! **`localsym`: la simetría que la prueba usa, y solo ésa.** En cada estado intermedio de las pasadas
de padres e hijos, para cada tramo (de abajo arriba) se toman las entradas comunes `r₀` del paso
justo debajo del tramo (y, en espejo, del paso justo encima): ¿tiene `r₀` a todos los miembros del
tramo en su tabla? Se cuenta por pares (tramo, `r₀`) —la versión «para toda»— y por tramo —«existe
alguna `r₀` simétrica»—, que es lo que la prueba necesita. -/

partial def collectDown (g : GPathM) (P : List PathNodeId) (acc : List (List PathNodeId) × Nat) :
    List (List PathNodeId) × Nat :=
  let (out, budget) := acc
  if budget == 0 then acc
  else
    match P with
    | [] => acc
    | low :: _ =>
      let ps := match g.node? low with
        | some n => n.parents.filter (fun p => P.all (fun y => mutuallyOwn g p y))
        | none => []
      ps.foldl (fun acc p => collectDown g (p :: P) acc) (P :: out, budget - 1)

structure LSCell where
  states : Nat := 0
  segs   : Nat := 0
  pairs  : Nat := 0
  pairsBad : Nat := 0
  segsWith : Nat := 0     -- tramos con alguna r₀ (hay entrada común en el paso)
  segsNone : Nat := 0     -- ... y ninguna r₀ es simétrica
  badDead : Nat := 0      -- r₀ no simétricas que no son nodo vivo
  first  : String := ""
  deriving Repr

def commonAt (g : GPathM) (P : List PathNodeId) (i : Int) : List PathNodeId :=
  match P with
  | [] => []
  | x :: rest => (ownersAt (tableOfAO g x) i).filter (fun r => rest.all (fun y => (tableOfAO g y).contains r))

def checkLS (label : String) (g : GPathM) (cap budget : Nat) (c : LSCell) : LSCell := Id.run do
  if !isValid g then return c
  let mut c := { c with states := c.states + 1 }
  for n in g.nodes.take cap do
    let (segs, _) := collectDown g [n.id] ([], budget)
    for P in segs do
      c := { c with segs := c.segs + 1 }
      -- abajo: P va de abajo arriba
      for (edge, i) in [(P.head?, (P.head?.map (·.id.step)).getD 0 - 1),
                        (P.getLast?, (P.getLast?.map (·.id.step)).getD 0 + 1)] do
        if edge.isSome && i ≥ 0 && i < g.current_step then
          let rs := commonAt g P i
          if !rs.isEmpty then
            let sym := rs.filter (fun r => P.all (fun y => (tableOfAO g r).contains y))
            let dead := (rs.filter (fun r => !(P.all (fun y => (tableOfAO g r).contains y)) && (g.node? r).isNone)).length
            c := { c with pairs := c.pairs + rs.length, pairsBad := c.pairsBad + (rs.length - sym.length)
                        , badDead := c.badDead + dead
                        , segsWith := c.segsWith + 1
                        , segsNone := c.segsNone + (if sym.isEmpty then 1 else 0)
                        , first := if c.first == "" && sym.isEmpty then
                            s!"{label} tramo {P.map (·.id.step)} paso {i}" else c.first }
  return c

structure LSAcc where
  formulas : Nat := 0
  par  : LSCell := {}
  sons : LSCell := {}
  deriving Repr

def instrStepsLS (lab : String) (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int)
    (cap budget : Nat) (c0 : LSCell) : GPathM × LSCell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      g := reviewNode g nb id
      c := checkLS s!"{lab} nodo@{id.id.step}" g cap budget c
  return (g, c)

def reviewLS (lab : String) (F : GPathM) (cap budget : Nat) (a : LSAcc) : LSAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        let h := cleanInvalid g
        let (h2, cp) := instrStepsLS s!"{lab} padres" h (·.parents) (intRange 1 (h.current_step - 1)) cap budget a.par
        a := { a with par := cp }
        let (h3, cs) := instrStepsLS s!"{lab} hijos" h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse cap budget a.sons
        a := { a with sons := cs }
        g := h3
        if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g2 := AggressiveReview.aggSweep g
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  return a

def runFormulaLS (label : String) (φ : Cnf) (cap budget : Nat) (a : LSAcc) : LSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewLS s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

def reportLS (name : String) (a : LSAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  let row (lbl : String) (c : LSCell) : IO Unit := do
    IO.println s!"   {lbl}: estados {c.states}, tramos {c.segs}"
    IO.println s!"      pares (tramo, r₀) {c.pairs}, r₀ NO simetrica {c.pairsBad} (de ellas, id de nodo muerto: {c.badDead})"
    IO.println s!"      bordes con alguna r₀ {c.segsWith}, sin ninguna r₀ simetrica {c.segsNone}"
    if c.first != "" then IO.println s!"      primero: {c.first}"
  row "pasada padres, por nodo" a.par
  row "pasada hijos, por nodo " a.sons
  IO.println s!"   ({ms} ms)"

/-! **`sweeppairs`: `SegGood` tras cada `aggPair` del barrido.** Se rehace `aggSweep` a mano, par a
par, dentro de `reviewAgg` de cada envío, y se mide `SegGood` tras cada par que cambia algo y tras
cada nodo borrado. -/

structure SPAcc where
  formulas : Nat := 0
  sweeps : Nat := 0
  fired : Nat := 0
  removed : Nat := 0
  pairs : TGCell := {}
  removes : TGCell := {}
  deriving Repr

def aggNodeInstr (lab : String) (g0 : GPathM) (x : PathNodeId) (cap budget : Nat) (a : SPAcc) :
    GPathM × SPAcc := Id.run do
  let mut g := g0
  let mut a := a
  match g.node? x with
  | none => return (g, a)
  | some nx =>
    if isValidNode g nx then
      for kw in (intRange 0 (g.current_step - 1)).reverse do
        for w in AggressiveReview.ownersAtNow g x kw do
          let g' := AggressiveReview.aggPair g x w
          if GPathM.measure g' < GPathM.measure g then
            a := { a with fired := a.fired + 1 }
            a := { a with pairs := measureSEG s!"{lab} par {x.id.step}/{w.id.step}" g' cap budget a.pairs }
          g := g'
    match g.node? x with
    | none => return (g, a)
    | some n1 =>
      if isValidNode g n1 then return (g, a)
      else
        let g' := removeNode g x
        a := { a with removed := a.removed + 1 }
        a := { a with removes := measureSEG s!"{lab} borra {x.id.step}" g' cap budget a.removes }
        return (g', a)

def sweepInstr (lab : String) (g0 : GPathM) (cap budget : Nat) (a : SPAcc) : GPathM × SPAcc := Id.run do
  if !isValid g0 then return (g0, a)
  let mut g := g0
  let mut a := a
  for k in (intRange 0 (g0.current_step - 1)).reverse do
    for id in (g.line k).map (·.id) do
      let (g', a') := aggNodeInstr lab g id cap budget a
      g := g'
      a := a'
  return (g, a)

def reviewSP (lab : String) (F : GPathM) (cap budget : Nat) (a : SPAcc) : SPAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    g := review g
    if !isValid g then outer := 0
    else
      let (g2, a') := sweepInstr lab g cap budget a
      a := { a' with sweeps := a'.sweeps + 1 }
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  return a

def runFormulaSP (label : String) (φ : Cnf) (cap budget : Nat) (a : SPAcc) : SPAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewSP s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  return a

def reportSP (name : String) (a : SPAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   barridos {a.sweeps}, pares que quitan algo {a.fired}, nodos borrados {a.removed}"
  let row (lbl : String) (c : TGCell) : IO Unit := do
    IO.println s!"   {lbl}: estados {c.states} (con fallo {c.statesBad}), tramos {c.chains}, sin entrada comun {c.bad}"
    if c.first != "" then IO.println s!"      primero: {c.first}"
  row "tras cada aggPair que quita algo" a.pairs
  row "tras cada nodo borrado          " a.removes
  IO.println s!"   ({ms} ms)"

/-! **`sweepcheck`: con las funciones reales.** En cada envío, `G = review F`: ¿`aggSweep G` quita
algo? ¿`reviewAgg F` difiere de `review F`? Y lo mismo en los pines del lector. -/

structure SCAcc where
  formulas : Nat := 0
  sends : Nat := 0
  sweepFires : Nat := 0
  aggDiffers : Nat := 0
  pins : Nat := 0
  pinFires : Nat := 0
  pinDiffers : Nat := 0
  deriving Repr

def nodeCount (g : GPathM) : Nat × Nat := (g.nodes.length, GPathM.measure g)

partial def walkSC (g : GPathM) (fuel : Nat) (a : SCAcc) : SCAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        let F := [q.id].foldl filterRequire g
        let G := review F
        a := { a with pins := a.pins + 1 }
        if isValid G then
          if GPathM.measure (AggressiveReview.aggSweep G) < GPathM.measure G then
            a := { a with pinFires := a.pinFires + 1 }
        if GPathM.measure (AggressiveReview.reviewAgg F) != GPathM.measure G then
          a := { a with pinDiffers := a.pinDiffers + 1 }
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkSC (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaSC (φ : Cnf) (a : SCAcc) : SCAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        let G := review F
        a := { a with sends := a.sends + 1 }
        if isValid G then
          if GPathM.measure (AggressiveReview.aggSweep G) < GPathM.measure G then
            a := { a with sweepFires := a.sweepFires + 1 }
        if GPathM.measure (AggressiveReview.reviewAgg F) != GPathM.measure G then
          a := { a with aggDiffers := a.aggDiffers + 1 }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkSC g (stepCount φ).toNat a
  return a

def reportSC (name : String) (a : SCAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   CONSTRUCCION: envios {a.sends}, aggSweep(review F) quita algo: {a.sweepFires}, reviewAgg F ≠ review F: {a.aggDiffers}"
  IO.println s!"   LECTOR      : pines {a.pins}, aggSweep(review F) quita algo: {a.pinFires}, reviewAgg F ≠ review F: {a.pinDiffers}"
  IO.println s!"   ({ms} ms)"

/-! **`extfire`: `ExtCtx` en los barridos que disparan.** Se rehace `reviewAgg` en cada envío (y en
cada pin del lector) y, en el barrido, antes de cada `aggPair` que quita algo se comprueban las
piezas de `ExtCtx` en el estado de antes: (I1), (I1-hijos), padres e hijos vivos, cada nodo se posee,
y la simetría local entre nodos vivos por los dos bordes. Tras el par, `SegGood`. -/

structure EFAcc where
  formulas : Nat := 0
  sweeps   : Nat := 0
  fired    : Nat := 0
  i1 : Nat := 0
  i1s : Nat := 0
  plive : Nat := 0
  slive : Nat := 0
  self : Nat := 0
  lsymLive : Nat := 0
  lsymNone : Nat := 0
  segAfter : TGCell := {}
  first : String := ""
  deriving Repr

def extChecks (g : GPathM) (cap budget : Nat) : Bool × Bool × Bool × Bool × Bool × Bool × Bool := Id.run do
  let mut b1 := false
  let mut b4 := false
  let mut bp := false
  let mut bs := false
  let mut bself := false
  for n in g.nodes do
    if !n.owners.contains n.id then bself := true
    for p in n.parents do
      if (g.node? p).isNone then bp := true
    for q in n.sons do
      if (g.node? q).isNone then bs := true
    for w in n.owners do
      if w.id.step + 1 == n.id.id.step && !n.parents.contains w then b1 := true
      if w.id.step == n.id.id.step + 1 && !n.sons.contains w then b4 := true
  let c := checkLS "" g cap budget {}
  let live := c.pairsBad - c.badDead
  return (b1, b4, bp, bs, bself, live > 0, c.segsNone > 0)

def sweepEF (lab : String) (g0 : GPathM) (cap budget : Nat) (a : EFAcc) : GPathM × EFAcc := Id.run do
  let mut g := g0
  let mut a := { a with sweeps := a.sweeps + 1 }
  for k in (intRange 0 (g0.current_step - 1)).reverse do
    for x in (g.line k).map (·.id) do
      match g.node? x with
      | none => pure ()
      | some nx =>
        if isValidNode g nx then
          for kw in (intRange 0 (g.current_step - 1)).reverse do
            for w in AggressiveReview.ownersAtNow g x kw do
              let g' := AggressiveReview.aggPair g x w
              if GPathM.measure g' < GPathM.measure g then
                let (b1, b4, bp, bs, bself, bls, bnone) := extChecks g cap budget
                a := { a with fired := a.fired + 1
                            , i1 := a.i1 + (if b1 then 1 else 0), i1s := a.i1s + (if b4 then 1 else 0)
                            , plive := a.plive + (if bp then 1 else 0), slive := a.slive + (if bs then 1 else 0)
                            , self := a.self + (if bself then 1 else 0)
                            , lsymLive := a.lsymLive + (if bls then 1 else 0)
                            , lsymNone := a.lsymNone + (if bnone then 1 else 0)
                            , first := if a.first == "" && (b1 || b4 || bp || bs || bself || bls) then
                                s!"{lab} par {x.id.step}/{w.id.step} I1={b1} I1s={b4} pvivos={!bp} hvivos={!bs} self={!bself} locsym={!bls}"
                              else a.first }
                a := { a with segAfter := measureSEG s!"{lab} tras par" g' cap budget a.segAfter }
              g := g'
        match g.node? x with
        | none => pure ()
        | some n1 => if !isValidNode g n1 then g := removeNode g x
  return (g, a)

def reviewAggEF (lab : String) (F : GPathM) (cap budget : Nat) (a : EFAcc) : EFAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    g := review g
    if !isValid g then outer := 0
    else
      let (g2, a') := sweepEF lab g cap budget a
      a := a'
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  return a

partial def walkEF (lab : String) (g : GPathM) (fuel cap budget : Nat) (a : EFAcc) : EFAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := reviewAggEF s!"{lab} pin" ([q.id].foldl filterRequire g) cap budget a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkEF lab (filterAllAgg g [q.id]) (fuel - 1) cap budget a

def runFormulaEF (label : String) (φ : Cnf) (cap budget : Nat) (a : EFAcc) : EFAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewAggEF s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkEF s!"{label} lector" g (stepCount φ).toNat cap budget a
  return a

def reportEF (name : String) (a : EFAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   barridos {a.sweeps}, pares que disparan {a.fired}"
  IO.println s!"   estados de antes del par que violan: (I1) {a.i1}, (I1-hijos) {a.i1s}, padres vivos {a.plive}, hijos vivos {a.slive}, self {a.self}, simetria local (vivos) {a.lsymLive}; bordes SIN ninguna entrada comun simetrica: {a.lsymNone}"
  IO.println s!"   SegGood tras el par: estados {a.segAfter.states}, con fallo {a.segAfter.statesBad}, tramos sin entrada comun {a.segAfter.bad}"
  if a.first != "" then IO.println s!"   primero: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`fullext`: «todo tramo se extiende a una cadena completa».** Para cada tramo (enlazado, poseído
por pares) se busca, con retroceso y presupuesto, una extensión hasta el paso 0 y hasta la cima: en
cada borde, candidatas = nodos vivos enlazados (padre del más bajo / hijo del más alto) que están en
todas las tablas del tramo y lo tienen entero en la suya. Se cuentan tramos que se extienden, que
NO (búsqueda exhaustiva) y los que agotan el presupuesto. -/

def fitsAll (g : GPathM) (P : List PathNodeId) (r : PathNodeId) : Bool :=
  match g.node? r with
  | none => false
  | some nr => P.all (fun y => nr.owners.contains y && (tableOfAO g y).contains r)

/-- `some true` se extiende, `some false` no (exhaustivo), `none` presupuesto agotado. -/
partial def extendFull (g : GPathM) (P : List PathNodeId) (budget : Nat) : Option Bool × Nat :=
  if budget == 0 then (none, 0)
  else
    match P.head?, P.getLast? with
    | some low, some high =>
      if low.id.step > 0 then
        let cands := match g.node? low with
          | some n => n.parents.filter (fun r => fitsAll g P r)
          | none => []
        cands.foldl (fun (acc : Option Bool × Nat) r =>
          match acc with
          | (some true, b) => (some true, b)
          | (res, b) =>
            if b == 0 then (none, 0)
            else
              let (r', b') := extendFull g (r :: P) (b - 1)
              match r', res with
              | some true, _ => (some true, b')
              | none, _ => (none, b')
              | some false, none => (none, b')
              | some false, _ => (some false, b'))
          (some false, budget)
      else if high.id.step < g.current_step - 1 then
        let cands := match g.node? high with
          | some n => n.sons.filter (fun r => fitsAll g P r &&
              (match g.node? r with | some nr => nr.parents.contains high | none => false))
          | none => []
        cands.foldl (fun (acc : Option Bool × Nat) r =>
          match acc with
          | (some true, b) => (some true, b)
          | (res, b) =>
            if b == 0 then (none, 0)
            else
              let (r', b') := extendFull g (P ++ [r]) (b - 1)
              match r', res with
              | some true, _ => (some true, b')
              | none, _ => (none, b')
              | some false, none => (none, b')
              | some false, _ => (some false, b'))
          (some false, budget)
      else (some true, budget)
    | _, _ => (some true, budget)

structure FXCell where
  states : Nat := 0
  segs   : Nat := 0
  bad    : Nat := 0
  cut    : Nat := 0
  statesBad : Nat := 0
  first  : String := ""
  deriving Repr

def measureFX (label : String) (g : GPathM) (cap budget : Nat) (c : FXCell) : FXCell := Id.run do
  if !isValid g then return c
  let mut c := { c with states := c.states + 1 }
  let mut anyBad := false
  for n in g.nodes.take cap do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      let (r, _) := extendFull g P budget
      c := { c with segs := c.segs + 1 }
      match r with
      | some true => pure ()
      | some false =>
        anyBad := true
        c := { c with bad := c.bad + 1
                    , first := if c.first == "" then s!"{label} tramo {P.map (·.id.step)}" else c.first }
      | none => c := { c with cut := c.cut + 1 }
  return { c with statesBad := c.statesBad + (if anyBad then 1 else 0) }

structure FXAcc where
  formulas : Nat := 0
  line   : FXCell := {}
  base   : FXCell := {}
  agg    : FXCell := {}
  up     : FXCell := {}
  reader : FXCell := {}
  clean  : FXCell := {}
  par    : FXCell := {}
  sons   : FXCell := {}
  pairs  : FXCell := {}
  deriving Repr

def instrStepsFX (lab : String) (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int)
    (cap budget : Nat) (c0 : FXCell) : GPathM × FXCell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      g := reviewNode g nb id
      c := measureFX s!"{lab} nodo@{id.id.step}" g cap budget c
  return (g, c)

def sweepFX (lab : String) (g0 : GPathM) (cap budget : Nat) (a : FXAcc) : GPathM × FXAcc := Id.run do
  let mut g := g0
  let mut a := a
  for k in (intRange 0 (g0.current_step - 1)).reverse do
    for x in (g.line k).map (·.id) do
      match g.node? x with
      | none => pure ()
      | some nx =>
        if isValidNode g nx then
          for kw in (intRange 0 (g.current_step - 1)).reverse do
            for w in AggressiveReview.ownersAtNow g x kw do
              let g' := AggressiveReview.aggPair g x w
              if GPathM.measure g' < GPathM.measure g then
                a := { a with pairs := measureFX s!"{lab} par {x.id.step}/{w.id.step}" g' cap budget a.pairs }
              g := g'
        match g.node? x with
        | none => pure ()
        | some n1 => if !isValidNode g n1 then g := removeNode g x
  return (g, a)

def reviewAggFX (lab : String) (F : GPathM) (cap budget : Nat) (a : FXAcc) : GPathM × FXAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        let mut h := g
        for id in g.nodes.map (·.id) do
          h := cleanInvalidGo h [id]
        a := { a with clean := measureFX s!"{lab} cleanInvalid" h cap budget a.clean }
        let (h2, cp) := instrStepsFX s!"{lab} padres" h (·.parents) (intRange 1 (h.current_step - 1)) cap budget a.par
        a := { a with par := cp }
        let (h3, cs) := instrStepsFX s!"{lab} hijos" h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse cap budget a.sons
        a := { a with sons := cs }
        g := h3
        if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      a := { a with base := measureFX s!"{lab} review" g cap budget a.base }
      let (g2, a') := sweepFX lab g cap budget a
      a := a'
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  return (g, a)

partial def walkFX (lab : String) (g : GPathM) (fuel cap budget : Nat) (a : FXAcc) : FXAcc :=
  if fuel == 0 then a
  else
    let a := { a with reader := measureFX s!"{lab} lector" g cap budget a.reader }
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        let (_, a') := reviewAggFX s!"{lab} pin" ([q.id].foldl filterRequire g) cap budget a
        a := a'
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkFX lab (filterAllAgg g [q.id]) (fuel - 1) cap budget a

def runFormulaFX (label : String) (φ : Cnf) (cap budget : Nat) (a : FXAcc) : FXAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := { a with line := measureFX s!"{label} paso {step} linea" kv.2 cap budget a.line }
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        let lab := s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩"
        let (R, a') := reviewAggFX lab F cap budget a
        a := a'
        if isValid R then
          a := { a with agg := measureFX s!"{lab} agg" R cap budget a.agg
                      , up := measureFX s!"{lab} up" (addNode R d "") cap budget a.up }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkFX s!"{label} lector" g (stepCount φ).toNat cap budget a
  return a

def reportFX (name : String) (a : FXAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  let row (lbl : String) (c : FXCell) : IO Unit := do
    IO.println s!"   {lbl}: estados {c.states} (con fallo {c.statesBad}), tramos {c.segs}, NO se extienden {c.bad}, presupuesto agotado {c.cut}"
    if c.first != "" then IO.println s!"      primero: {c.first}"
  row "linea (tras doJoin)      " a.line
  row "tras cleanInvalid (pasada)" a.clean
  row "pasada padres, por nodo  " a.par
  row "pasada hijos, por nodo   " a.sons
  row "revision base (review)   " a.base
  row "barrido, por par         " a.pairs
  row "review agresivo  [REV]   " a.agg
  row "up                       " a.up
  row "lector           [REV]   " a.reader
  IO.println s!"   ({ms} ms)"

/-! **`cleanobl`: la obligación de `cleanInvalid`.** En cada `cleanInvalid` real (construcción y pines
del lector): para cada tramo del estado DE DESPUÉS, ¿se extiende en el estado DE ANTES a una cadena
completa cuyos miembros están todos en la tabla global FINAL? Y, por comparar, sin esa restricción. -/

partial def extendFullIn (g : GPathM) (ok : PathNodeId → Bool) (P : List PathNodeId) (budget : Nat) :
    Option Bool × Nat :=
  if budget == 0 then (none, 0)
  else
    match P.head?, P.getLast? with
    | some low, some high =>
      let step (cands : List PathNodeId) (mk : PathNodeId → List PathNodeId) : Option Bool × Nat :=
        cands.foldl (fun (acc : Option Bool × Nat) r =>
          match acc with
          | (some true, b) => (some true, b)
          | (res, b) =>
            if b == 0 then (none, 0)
            else
              let (r', b') := extendFullIn g ok (mk r) (b - 1)
              match r', res with
              | some true, _ => (some true, b')
              | none, _ => (none, b')
              | some false, none => (none, b')
              | some false, _ => (some false, b'))
          (some false, budget)
      if low.id.step > 0 then
        let cands := match g.node? low with
          | some n => n.parents.filter (fun r => ok r && fitsAll g P r)
          | none => []
        step cands (fun r => r :: P)
      else if high.id.step < g.current_step - 1 then
        let cands := match g.node? high with
          | some n => n.sons.filter (fun r => ok r && fitsAll g P r &&
              (match g.node? r with | some nr => nr.parents.contains high | none => false))
          | none => []
        step cands (fun r => P ++ [r])
      else (some true, budget)
    | _, _ => (some true, budget)

structure COAcc where
  formulas : Nat := 0
  passes : Nat := 0
  segs : Nat := 0
  inGow : Nat := 0       -- se extiende en el de antes dentro de la global final
  anyExt : Nat := 0      -- se extiende en el de antes (sin restricción)
  none_ : Nat := 0       -- no se extiende dentro de la global final (exhaustivo)
  cut : Nat := 0
  first : String := ""
  deriving Repr

def checkClean (lab : String) (G : GPathM) (cap budget : Nat) (a : COAcc) : COAcc := Id.run do
  let G' := cleanInvalid G
  if !isValid G' then return a
  let mut a := { a with passes := a.passes + 1 }
  let gow := G'.gowners
  for n in G'.nodes.take cap do
    let (segs, _) := collectDown G' [n.id] ([], 60)
    for P in segs do
      if P.all (fun x => (G.node? x).isSome) then
        a := { a with segs := a.segs + 1 }
        let (r1, _) := extendFullIn G (fun r => gow.contains r) P budget
        let (r2, _) := extendFull G P budget
        match r1 with
        | some true => a := { a with inGow := a.inGow + 1 }
        | some false => a := { a with none_ := a.none_ + 1
                                    , first := if a.first == "" then s!"{lab} tramo {P.map (·.id.step)}" else a.first }
        | none => a := { a with cut := a.cut + 1 }
        if r2 == some true then a := { a with anyExt := a.anyExt + 1 }
  return a

def reviewCO (lab : String) (F : GPathM) (cap budget : Nat) (a : COAcc) : COAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure F + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        a := checkClean lab g cap budget a
        let g3 := reviewSons (reviewParents (cleanInvalid g))
        g := g3
        if !(GPathM.measure g3 < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g2 := AggressiveReview.aggSweep g
      if GPathM.measure g2 < GPathM.measure g then g := g2 else outer := 0
  return a

partial def walkCO (lab : String) (g : GPathM) (fuel cap budget : Nat) (a : COAcc) : COAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := reviewCO s!"{lab} pin" ([q.id].foldl filterRequire g) cap budget a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkCO lab (filterAllAgg g [q.id]) (fuel - 1) cap budget a

def runFormulaCO (label : String) (φ : Cnf) (cap budget : Nat) (a : COAcc) : COAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewCO s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkCO s!"{label} lector" g (stepCount φ).toNat cap budget a
  return a

def reportCO (name : String) (a : COAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   pasadas de cleanInvalid validas {a.passes}, tramos del estado de despues {a.segs}"
  IO.println s!"     se extienden en el de ANTES dentro de la global FINAL: {a.inGow}"
  IO.println s!"     NO (busqueda exhaustiva)                          : {a.none_}"
  IO.println s!"     presupuesto agotado                               : {a.cut}"
  IO.println s!"     (sin la restriccion de la global: {a.anyExt})"
  if a.first != "" then IO.println s!"   primero que no: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`filterkill`: ¿el review mata exactamente los tramos que el filtro deja sin extensión?** Justo tras
el filtro (antes del review), para cada tramo con todos sus miembros en la tabla global: ¿se extiende
dentro de ella? Y, tras `reviewAgg`, ¿sigue siendo tramo? -/

structure FKAcc where
  formulas : Nat := 0
  states : Nat := 0
  segs : Nat := 0
  ext : Nat := 0
  extSurv : Nat := 0
  noext : Nat := 0
  noextSurv : Nat := 0
  cut : Nat := 0
  first : String := ""
  deriving Repr

def checkFK (lab : String) (F : GPathM) (cap budget : Nat) (a : FKAcc) : FKAcc := Id.run do
  let R := AggressiveReview.reviewAgg F
  let mut a := { a with states := a.states + 1 }
  let gow := F.gowners
  for n in F.nodes.take cap do
    if gow.contains n.id then
      let (segs, _) := collectDown F [n.id] ([], 60)
      for P in segs do
        if P.all (fun x => gow.contains x) then
          a := { a with segs := a.segs + 1 }
          let surv := isValid R && isSegment R P
          match (extendFullIn F (fun r => gow.contains r) P budget).1 with
          | some true => a := { a with ext := a.ext + 1, extSurv := a.extSurv + (if surv then 1 else 0) }
          | some false =>
            a := { a with noext := a.noext + 1, noextSurv := a.noextSurv + (if surv then 1 else 0)
                        , first := if a.first == "" && surv then s!"{lab} tramo {P.map (·.id.step)}" else a.first }
          | none => a := { a with cut := a.cut + 1 }
  return a

partial def walkFK (lab : String) (g : GPathM) (fuel cap budget : Nat) (a : FKAcc) : FKAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := checkFK s!"{lab} pin" ([q.id].foldl filterRequire g) cap budget a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkFK lab (filterAllAgg g [q.id]) (fuel - 1) cap budget a

def runFormulaFK (label : String) (φ : Cnf) (cap budget : Nat) (a : FKAcc) : FKAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := checkFK s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkFK s!"{label} lector" g (stepCount φ).toNat cap budget a
  return a

def reportFK (name : String) (a : FKAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.states} estados filtrados)"
  IO.println s!"   tramos dentro de la global tras el filtro: {a.segs}"
  IO.println s!"     se extienden dentro de la global     : {a.ext}  (sobreviven al review: {a.extSurv})"
  IO.println s!"     NO se extienden (exhaustivo)         : {a.noext}  (sobreviven al review: {a.noextSurv})"
  IO.println s!"     presupuesto agotado                  : {a.cut}"
  if a.first != "" then IO.println s!"   primero que NO se extiende y SOBREVIVE: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`joinext`: ¿la unión conserva `FullExtG`?** En cada unión real de la línea, `J = join A B` (con
`okJoin`): para cada tramo de `J` con todos sus miembros en la tabla global de `J`, ¿se extiende a una
cadena completa dentro de ella? Se cuenta también si el tramo es tramo de `A` o de `B` (o de
ninguno: **mezclado**), y si los lados cumplían `FullExtG` (la hipótesis de `JoinFullExt`). -/

structure JXAcc where
  formulas : Nat := 0
  joins : Nat := 0
  segs : Nat := 0
  inA : Nat := 0
  inB : Nat := 0
  mixed : Nat := 0
  ext : Nat := 0
  noext : Nat := 0
  noextMixed : Nat := 0
  cut : Nat := 0
  sideSegs : Nat := 0
  sideBad : Nat := 0
  cleanJoins : Nat := 0
  cleanNoext : Nat := 0
  cleanBadJoins : Nat := 0
  revSurv : Nat := 0
  first : String := ""
  deriving Repr

/-- Tramos dentro de la global de `g` que no se extienden dentro de ella (exhaustivo), y cuántos. -/
def sideFX (g : GPathM) (cap budget : Nat) : Nat × Nat := Id.run do
  let gow := g.gowners
  let mut n := 0
  let mut bad := 0
  for x in g.nodes.take cap do
    if gow.contains x.id then
      let (segs, _) := collectDown g [x.id] ([], 60)
      for P in segs do
        if P.all (fun y => gow.contains y) then
          n := n + 1
          if (extendFullIn g (fun r => gow.contains r) P budget).1 == some false then bad := bad + 1
  return (n, bad)

def checkJX (lab : String) (A B : GPathM) (cap budget : Nat) (a : JXAcc) : JXAcc := Id.run do
  if !(okJoin A B) then return a
  let J := join A B
  let mut a := { a with joins := a.joins + 1 }
  let (na, ba) := sideFX A cap budget
  let (nb, bb) := sideFX B cap budget
  a := { a with sideSegs := a.sideSegs + na + nb, sideBad := a.sideBad + ba + bb }
  let clean := ba + bb == 0
  let before := a.noext
  let R := AggressiveReview.reviewAgg J
  let gow := J.gowners
  for n in J.nodes.take cap do
    if gow.contains n.id then
      let (segs, _) := collectDown J [n.id] ([], 60)
      for P in segs do
        if P.all (fun x => gow.contains x) then
          let ia := isSegment A P && P.all (fun x => A.gowners.contains x)
          let ib := isSegment B P && P.all (fun x => B.gowners.contains x)
          let mix := !ia && !ib
          a := { a with segs := a.segs + 1, inA := a.inA + (if ia then 1 else 0)
                      , inB := a.inB + (if ib then 1 else 0), mixed := a.mixed + (if mix then 1 else 0) }
          match (extendFullIn J (fun r => gow.contains r) P budget).1 with
          | some true => a := { a with ext := a.ext + 1 }
          | some false =>
            a := { a with noext := a.noext + 1, noextMixed := a.noextMixed + (if mix then 1 else 0)
                        , revSurv := a.revSurv + (if isValid R && isSegment R P then 1 else 0)
                        , first := if a.first == "" && clean then
                            s!"{lab} tramo {P.map (·.id.step)} mezclado={mix}" else a.first }
          | none => a := { a with cut := a.cut + 1 }
  if clean then
    a := { a with cleanJoins := a.cleanJoins + 1, cleanNoext := a.cleanNoext + (a.noext - before)
                , cleanBadJoins := a.cleanBadJoins + (if a.noext > before then 1 else 0) }
  return a

def runFormulaJX (label : String) (φ : Cnf) (cap budget : Nat) (a : JXAcc) : JXAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let h := upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
        if isValid h then
          match next.find? (fun e => e.1 == d) with
          | some (_, existing) =>
            a := checkJX s!"{label} paso {step} →⟨{d.step},{d.index}⟩" existing h cap budget a
            next := next.map (fun e => if e.1 == d then (d, doJoin existing h) else e)
          | none => next := next ++ [(d, h)]
    line := next
  return a

def reportJX (name : String) (a : JXAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.joins} uniones)"
  IO.println s!"   lados: {a.sideSegs} tramos, sin extension {a.sideBad}"
  IO.println s!"   tramos de la union dentro de su global: {a.segs}"
  IO.println s!"     de A: {a.inA}   de B: {a.inB}   MEZCLADOS: {a.mixed}"
  IO.println s!"     se extienden: {a.ext}   NO se extienden: {a.noext} (mezclados: {a.noextMixed})   presupuesto: {a.cut}"
  IO.println s!"     de ellos sobreviven al review agresivo de la union: {a.revSurv}"
  IO.println s!"   uniones con los dos lados limpios: {a.cleanJoins}, con tramo sin extension: {a.cleanBadJoins} ({a.cleanNoext} tramos)"
  if a.first != "" then IO.println s!"   primero sin extension (lados limpios): {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`ext1`: `FullExtG` solo para tramos de UN nodo.** Cada entrada de la tabla global, ¿se extiende a
una cadena completa dentro de ella? En la línea (tras cada avance, con uniones), tras su review
agresivo, en los estados del lector (inicio y pines) y justo tras cada unión. -/

structure E1Cell where
  states : Nat := 0
  entries : Nat := 0
  bad : Nat := 0
  cut : Nat := 0
  first : String := ""
  deriving Repr

def checkE1 (lab : String) (g : GPathM) (budget : Nat) (c : E1Cell) : E1Cell := Id.run do
  if !isValid g then return c
  let gow := g.gowners
  let mut c := { c with states := c.states + 1 }
  for q in gow do
    c := { c with entries := c.entries + 1 }
    match (extendFullIn g (fun r => gow.contains r) [q] budget).1 with
    | some true => pure ()
    | some false => c := { c with bad := c.bad + 1
                                , first := if c.first == "" then s!"{lab} entrada @{q.id.step}" else c.first }
    | none => c := { c with cut := c.cut + 1 }
  return c

structure E1Acc where
  formulas : Nat := 0
  join : E1Cell := {}
  send : E1Cell := {}
  line : E1Cell := {}
  rev : E1Cell := {}
  reader : E1Cell := {}
  deriving Repr

partial def walkE1 (lab : String) (g : GPathM) (fuel budget : Nat) (c : E1Cell) : E1Cell :=
  let c := checkE1 lab g budget c
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := checkE1 s!"{lab} pin" (filterAllAgg g [q.id]) budget c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkE1 lab (filterAllAgg g [q.id]) (fuel - 1) budget c

def runFormulaE1 (label : String) (φ : Cnf) (budget : Nat) (a : E1Acc) : E1Acc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let h := upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
        if isValid h then
          let F := filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)
          a := { a with send := checkE1 s!"{label} envio paso {step}" F budget a.send }
          match next.find? (fun e => e.1 == d) with
          | some (_, existing) =>
            if okJoin existing h then
              a := { a with join := checkE1 s!"{label} union paso {step}" (join existing h) budget a.join }
            next := next.map (fun e => if e.1 == d then (d, doJoin existing h) else e)
          | none => next := next ++ [(d, h)]
    line := next
    for kv in line do
      a := { a with line := checkE1 s!"{label} linea paso {step}" kv.2 budget a.line
                  , rev := checkE1 s!"{label} review paso {step}" (filterAllAgg kv.2 []) budget a.rev }
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with reader := walkE1 s!"{label} lector" g (stepCount φ).toNat budget a.reader }
  return a

def reportE1Cell (name : String) (c : E1Cell) : IO Unit := do
  IO.println s!"   {name}: estados {c.states}, entradas {c.entries}, NO se extienden {c.bad}, presupuesto {c.cut}"
  if c.first != "" then IO.println s!"      primera: {c.first}"

def reportE1 (name : String) (a : E1Acc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportE1Cell "envio revisado (antes del up)" a.send
  reportE1Cell "tras cada union      " a.join
  reportE1Cell "linea                " a.line
  reportE1Cell "linea + review       " a.rev
  reportE1Cell "lector (inicio, pines)" a.reader
  IO.println s!"   ({ms} ms)"

/-! **`pairext`: parejas con la frontera.** En cada estado del lector (inicio y pines, válidos), con
`k = firstChoice`: para cada entrada global `r` y cada entrada global `q'` del paso `k` que se poseen
(`q'` en la tabla de `r`, una sola dirección), ¿hay una cadena completa dentro de la global que pase por las dos? Si sí siempre, el pin
en `k` conserva `FullExt1` (`PinExt1`). -/

structure PXCell where
  states : Nat := 0
  pairs : Nat := 0
  bad : Nat := 0
  cut : Nat := 0
  first : String := ""
  deriving Repr

def checkPX (lab : String) (g : GPathM) (budget : Nat) (c : PXCell) : PXCell := Id.run do
  if !isValid g then return c
  match ReaderExec.firstChoice g with
  | none => return c
  | some k =>
    let gow := g.gowners
    let mut c := { c with states := c.states + 1 }
    for q' in ownersAt gow k do
      for r in gow do
        let owns := match g.node? r with | some nr => nr.owners.contains q' | none => false
        if r.id.step != k && owns then
          c := { c with pairs := c.pairs + 1 }
          let ok := fun x => gow.contains x && (x.id.step != k || x == q')
          match (extendFullIn g ok [r] budget).1 with
          | some true => pure ()
          | some false =>
            let msg := s!"{lab} k={k} r@{r.id.step}"
            c := { c with bad := c.bad + 1, first := if c.first == "" then msg else c.first }
          | none => c := { c with cut := c.cut + 1 }
    return c

partial def walkPX (lab : String) (g : GPathM) (fuel budget : Nat) (c : PXCell) : PXCell :=
  let c := checkPX lab g budget c
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := checkPX s!"{lab} pin" (filterAllAgg g [q.id]) budget c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkPX lab (filterAllAgg g [q.id]) (fuel - 1) budget c

def runFormulaPX (label : String) (φ : Cnf) (budget : Nat) (c : PXCell) : PXCell := Id.run do
  let mut c := c
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then c := walkPX s!"{label} lector" g (stepCount φ).toNat budget c
  return c

def reportPX (name : String) (c : PXCell) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}"
  IO.println s!"   estados del lector {c.states}, parejas (r, q' frontera) {c.pairs}, sin cadena comun {c.bad}, presupuesto {c.cut}"
  if c.first != "" then IO.println s!"   primera: {c.first}"
  IO.println s!"   ({ms} ms)"

/-! **`seqsend`: el envío como sucesión de filtros de un paso.** Para cada envío: `F` = todos los
filtros (débil y duros) y un review; `S` = cada filtro de un paso (`filterWeak (k, A)`; un requisito
duro es `(r.step, [r])`) seguido de su review. ¿Coinciden `F` y `S` (validez, tabla global, nodos y
sus tablas)? Y en cada filtro de un paso sobre un estado revisado `T`: para `r` en la global y `q'`
del paso filtrado en la tabla de `r`, ¿hay cadena completa común dentro de la global de `T`? -/

structure SQAcc where
  formulas : Nat := 0
  sends : Nat := 0
  same : Nat := 0
  diffValid : Nat := 0
  diffGow : Nat := 0
  diffNodes : Nat := 0
  stepFilters : Nat := 0
  pairs : Nat := 0
  pairsBad : Nat := 0
  cut : Nat := 0
  first : String := ""
  firstPair : String := ""
  deriving Repr

def sameSet (a b : List PathNodeId) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

def sameState (F S : GPathM) : Bool × Bool :=
  let gow := sameSet F.gowners S.gowners
  let nodes := sameSet (F.nodes.map (·.id)) (S.nodes.map (·.id)) &&
    F.nodes.all (fun n => match S.node? n.id with
      | some m => sameSet n.owners m.owners && sameSet n.parents m.parents && sameSet n.sons m.sons
      | none => false)
  (gow, nodes)

def pairsAt (T : GPathM) (k : Int) (budget : Nat) (a : SQAcc) (lab : String) : SQAcc := Id.run do
  let gow := T.gowners
  let mut a := a
  for q' in ownersAt gow k do
    for r in gow do
      let owns := match T.node? r with | some nr => nr.owners.contains q' | none => false
      if r.id.step != k && owns then
        a := { a with pairs := a.pairs + 1 }
        let ok := fun x => gow.contains x && (x.id.step != k || x == q')
        match (extendFullIn T ok [r] budget).1 with
        | some true => pure ()
        | some false =>
          let msg := s!"{lab} k={k} r@{r.id.step}"
          a := { a with pairsBad := a.pairsBad + 1, firstPair := if a.firstPair == "" then msg else a.firstPair }
        | none => a := { a with cut := a.cut + 1 }
  return a

def runFormulaSQ (label : String) (φ : Cnf) (budget : Nat) (a : SQAcc) : SQAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let lab := s!"{label} paso {step}"
        let F := filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        let mut dead := false
        a := { a with sends := a.sends + 1 }
        for e in es do
          if !dead then
            if isValid T then
              a := pairsAt T e.1 budget { a with stepFilters := a.stepFilters + 1 } lab
            T := AggressiveReview.reviewAgg (filterWeak T e)
            if !isValid T then dead := true
        let vF := isValid F
        let vS := isValid T
        if vF != vS then
          a := { a with diffValid := a.diffValid + 1
                      , first := if a.first == "" then s!"{lab} validez F={vF} S={vS}" else a.first }
        else if vF then
          let (sg, sn) := sameState F T
          if sg && sn then a := { a with same := a.same + 1 }
          else
            a := { a with diffGow := a.diffGow + (if sg then 0 else 1), diffNodes := a.diffNodes + (if sn then 0 else 1)
                        , first := if a.first == "" then s!"{lab} global={sg} nodos={sn}" else a.first }
        else a := { a with same := a.same + 1 }
    line := pureAdvanceW φ line
  return a

def reportSQ (name : String) (a : SQAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.sends} envios)"
  IO.println s!"   todo-de-una vs uno-a-uno: iguales {a.same}, distinta validez {a.diffValid}, distinta global {a.diffGow}, distintos nodos {a.diffNodes}"
  if a.first != "" then IO.println s!"   primera diferencia: {a.first}"
  IO.println s!"   filtros de un paso {a.stepFilters}: parejas {a.pairs}, sin cadena comun {a.pairsBad}, presupuesto {a.cut}"
  if a.firstPair != "" then IO.println s!"   primera pareja mala: {a.firstPair}"
  IO.println s!"   ({ms} ms)"

/-! **`pairall`: la tabla de owners dice la verdad, en todos los pasos.** En cada estado del lector
(inicio y pines, válidos): para toda entrada global `r` y toda `q'` global en la tabla de `r`, de
cualquier paso distinto, ¿hay una cadena completa dentro de la global por las dos? -/

def checkPA (lab : String) (g : GPathM) (budget : Nat) (c : PXCell) : PXCell := Id.run do
  if !isValid g then return c
  let gow := g.gowners
  let mut c := { c with states := c.states + 1 }
  for r in gow do
    match g.node? r with
    | none => pure ()
    | some nr =>
      for q' in nr.owners do
        if q'.id.step != r.id.step && gow.contains q' then
          c := { c with pairs := c.pairs + 1 }
          let k := q'.id.step
          let ok := fun x => gow.contains x && (x.id.step != k || x == q')
          match (extendFullIn g ok [r] budget).1 with
          | some true => pure ()
          | some false =>
            let msg := s!"{lab} r@{r.id.step} q'@{k}"
            c := { c with bad := c.bad + 1, first := if c.first == "" then msg else c.first }
          | none => c := { c with cut := c.cut + 1 }
  return c

partial def walkPA (lab : String) (g : GPathM) (fuel budget : Nat) (c : PXCell) : PXCell :=
  let c := checkPA lab g budget c
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := checkPA s!"{lab} pin" (filterAllAgg g [q.id]) budget c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkPA lab (filterAllAgg g [q.id]) (fuel - 1) budget c

def runFormulaPA (label : String) (φ : Cnf) (budget : Nat) (c : PXCell) : PXCell := Id.run do
  let mut c := c
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then c := walkPA s!"{label} lector" g (stepCount φ).toNat budget c
  return c

/-! **`pairline`: las tablas dicen la verdad en la línea y en los envíos paso a paso.** `checkPA` en cada
estado de la línea (tras cada avance) y en cada estado intermedio del envío uno a uno (`seqsend`). -/

structure PLAcc where
  formulas : Nat := 0
  line : PXCell := {}
  inter : PXCell := {}
  deriving Repr

def runFormulaPL (label : String) (φ : Cnf) (budget : Nat) (a : PLAcc) : PLAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := { a with line := checkPA s!"{label} linea paso {step}" kv.2 budget a.line }
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        a := { a with inter := checkPA s!"{label} envio paso {step} T0" T budget a.inter }
        for e in es do
          if isValid T then
            T := AggressiveReview.reviewAgg (filterWeak T e)
            a := { a with inter := checkPA s!"{label} envio paso {step} tras ({e.1})" T budget a.inter }
    line := pureAdvanceW φ line
  for kv in line do
    a := { a with line := checkPA s!"{label} linea final" kv.2 budget a.line }
  return a

def reportPL (name : String) (a : PLAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   linea: estados {a.line.states}, parejas {a.line.pairs}, sin cadena comun {a.line.bad}, presupuesto {a.line.cut}"
  if a.line.first != "" then IO.println s!"      primera: {a.line.first}"
  IO.println s!"   envio paso a paso: estados {a.inter.states}, parejas {a.inter.pairs}, sin cadena comun {a.inter.bad}, presupuesto {a.inter.cut}"
  if a.inter.first != "" then IO.println s!"      primera: {a.inter.first}"
  IO.println s!"   ({ms} ms)"

/-! **`triplestep`: las ternas que la prueba del filtro necesita.** En el envío paso a paso, para cada
filtro de un paso `e` (paso `k`) sobre `T`, con `R` = su review: para cada pareja `r`, `q'` de `R`
(`q'` en la tabla de `r`, pasos distintos de `k`) y cada `c` del paso `k` en las dos tablas de `R`,
¿hay en `T` una cadena completa dentro de su global por `r`, `q'` y `c`? -/

structure T3Acc where
  formulas : Nat := 0
  filters : Nat := 0
  triples : Nat := 0
  bad : Nat := 0
  cut : Nat := 0
  first : String := ""
  deriving Repr

def checkT3 (lab : String) (T R : GPathM) (k : Int) (budget : Nat) (a : T3Acc) : T3Acc := Id.run do
  let gow := T.gowners
  let mut a := { a with filters := a.filters + 1 }
  for r in R.gowners do
    if r.id.step != k then
      match R.node? r with
      | none => pure ()
      | some nr =>
        for q' in nr.owners do
          if q'.id.step != k && q'.id.step != r.id.step && R.gowners.contains q' then
            match R.node? q' with
            | none => pure ()
            | some nq =>
              for c in ownersAt nr.owners k do
                if nq.owners.contains c then
                  a := { a with triples := a.triples + 1 }
                  let ok := fun x => gow.contains x && (x.id.step != q'.id.step || x == q') &&
                    (x.id.step != k || x == c)
                  match (extendFullIn T ok [r] budget).1 with
                  | some true => pure ()
                  | some false =>
                    let msg := s!"{lab} k={k} r@{r.id.step} q'@{q'.id.step}"
                    a := { a with bad := a.bad + 1, first := if a.first == "" then msg else a.first }
                  | none => a := { a with cut := a.cut + 1 }
  return a

def runFormulaT3 (label : String) (φ : Cnf) (budget : Nat) (a : T3Acc) : T3Acc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        for e in es do
          if isValid T then
            let R := AggressiveReview.reviewAgg (filterWeak T e)
            if isValid R then a := checkT3 s!"{label} paso {step}" T R e.1 budget a
            T := R
    line := pureAdvanceW φ line
  return a

def reportT3 (name : String) (a : T3Acc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.filters} filtros de un paso)"
  IO.println s!"   ternas (r, q', c del paso filtrado): {a.triples}, sin cadena en T: {a.bad}, presupuesto {a.cut}"
  if a.first != "" then IO.println s!"   primera: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`nest`: ¿las tablas se anidan a lo largo de una cadena de padres?** En los estados del lector
(inicio y pines, válidos): para cada tramo enlazado por padres y poseído por pares `c_lo … c_hi`
(`collectDown`), y cada miembro `y` por encima de `c_lo`: ¿la tabla de `c_lo`, por debajo de `lo`,
está en la tabla de `y`? Si sí, la tabla colectiva del descenso es la del último elegido. -/

structure NSAcc where
  formulas : Nat := 0
  states : Nat := 0
  segs : Nat := 0
  checks : Nat := 0
  bad : Nat := 0
  badTop : Nat := 0
  rev : Nat := 0
  revBad : Nat := 0
  revFirst : String := ""
  first : String := ""
  deriving Repr

def checkNS (lab : String) (g : GPathM) (a : NSAcc) : NSAcc := Id.run do
  if !isValid g then return a
  let mut a := { a with states := a.states + 1 }
  for n in g.nodes do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        a := { a with segs := a.segs + 1 }
        let top := (P.getLast?.map (fun x => x.id.step == g.current_step - 1)).getD false
        match g.node? low with
        | none => pure ()
        | some nl =>
          let below := nl.owners.filter (fun r => r.id.step < low.id.step)
          for y in P.drop 1 do
            match g.node? y with
            | none => pure ()
            | some ny =>
              a := { a with checks := a.checks + 1 }
              let ybelow := ny.owners.filter (fun r => r.id.step < low.id.step)
              a := { a with rev := a.rev + 1 }
              if !ybelow.all (fun r => nl.owners.contains r) then
                let msg := s!"{lab} low@{low.id.step} y@{y.id.step} tramo {P.map (·.id.step)}"
                a := { a with revBad := a.revBad + 1, revFirst := if a.revFirst == "" then msg else a.revFirst }
              if !below.all (fun r => ny.owners.contains r) then
                let msg := s!"{lab} low@{low.id.step} y@{y.id.step} tramo {P.map (·.id.step)}"
                a := { a with bad := a.bad + 1, badTop := a.badTop + (if top then 1 else 0)
                            , first := if a.first == "" then msg else a.first }
  return a

partial def walkNS (lab : String) (g : GPathM) (fuel : Nat) (a : NSAcc) : NSAcc :=
  let a := checkNS lab g a
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkNS lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaNS (label : String) (φ : Cnf) (a : NSAcc) : NSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkNS s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportNS (name : String) (a : NSAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.states} estados del lector)"
  IO.println s!"   tramos {a.segs}, comprobaciones {a.checks}, NO anidadas {a.bad} (tramos hasta la cima: {a.badTop})"
  if a.first != "" then IO.println s!"   primera: {a.first}"
  IO.println s!"   al reves (tabla de y por debajo de lo, dentro de la de c_lo): {a.rev}, NO {a.revBad}"
  if a.revFirst != "" then IO.println s!"   primera al reves: {a.revFirst}"
  IO.println s!"   ({ms} ms)"

/-! **`topkill`: ¿quién mata la cadena que el filtro deja sin entrada común?** Para cada filtro de un
paso `e` (paso `k`) sobre un estado revisado `T` —en el envío paso a paso y en los pines del
lector—: cadenas desde la cima de `T` (enlazadas, poseídas por pares) que están por encima de `k` y
cuya tabla colectiva en `T` no tiene en `k` ninguna entrada admitida. ¿Siguen siendo cadena tras el
review base? ¿Y tras el agresivo? -/

structure TKAcc where
  formulas : Nat := 0
  filters : Nat := 0
  chains : Nat := 0
  noAdm : Nat := 0
  deadBase : Nat := 0
  deadAgg : Nat := 0
  alive : Nat := 0
  first : String := ""
  deriving Repr

def checkTK (lab : String) (T : GPathM) (e : Int × List NodeId) (a : TKAcc) : TKAcc := Id.run do
  let k := e.1
  let X := filterWeak T e
  let B := review X
  let R := AggressiveReview.reviewAgg X
  let mut a := { a with filters := a.filters + 1 }
  for n in T.line (T.current_step - 1) do
    let (segs, _) := collectDown T [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        if low.id.step > k then
          a := { a with chains := a.chains + 1 }
          let tabs := P.filterMap (fun y => (T.node? y).map (·.owners))
          let common := match tabs.head? with
            | none => []
            | some t0 => (ownersAt t0 k).filter (fun r => tabs.all (fun t => t.contains r))
          if !common.any (fun r => e.2.contains r.id) then
            a := { a with noAdm := a.noAdm + 1 }
            let inB := isValid B && isSegment B P
            let inR := isValid R && isSegment R P
            if !inB then a := { a with deadBase := a.deadBase + 1 }
            else if !inR then a := { a with deadAgg := a.deadAgg + 1 }
            else
              a := { a with alive := a.alive + 1
                          , first := if a.first == "" then s!"{lab} k={k} cadena {P.map (·.id.step)}" else a.first }
  return a

partial def walkTK (lab : String) (g : GPathM) (fuel : Nat) (a : TKAcc) : TKAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := checkTK s!"{lab} pin" g (k, [q.id]) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkTK lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaTK (label : String) (φ : Cnf) (a : TKAcc) : TKAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        for e in es do
          if isValid T then
            a := checkTK s!"{label} envio paso {step}" T e a
            T := AggressiveReview.reviewAgg (filterWeak T e)
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkTK s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportTK (name : String) (a : TKAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.filters} filtros de un paso)"
  IO.println s!"   cadenas desde la cima por encima del paso filtrado: {a.chains}"
  IO.println s!"   sin entrada comun admitida: {a.noAdm}"
  IO.println s!"     mueren en el review base: {a.deadBase}   solo con el agresivo: {a.deadAgg}   SOBREVIVEN: {a.alive}"
  if a.first != "" then IO.println s!"   primera que sobrevive: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`toptrace`: cómo mata el review base la cadena sin entrada común admitida.** Para cada cadena de
`topkill` que se queda sin entrada común admitida en el paso filtrado `k`: ¿algún miembro se quedó
solo, ya sin ninguna entrada admitida en `k` en su propia tabla (muerte individual)? ¿O cada miembro
tiene alguna, pero no común (caso Helly)? Y se sigue el review base vuelta a vuelta y pasada a pasada
(`cleanInvalid`, padres, hijos) hasta la primera en que la cadena deja de serlo. -/

structure TTAcc where
  formulas : Nat := 0
  chains : Nat := 0
  indiv : Nat := 0
  helly : Nat := 0
  hellyLen : Nat := 0
  byStage : Array Nat := #[0, 0, 0, 0]
  hellyStage : Array Nat := #[0, 0, 0, 0]
  hellyRound1 : Nat := 0
  examples : List String := []
  deriving Repr

def stageOfDeath (X : GPathM) (P : List PathNodeId) (fuel : Nat) : Nat × Nat := Id.run do
  let mut g := X
  for r in [0:fuel] do
    if !isValid g then return (0, r)
    let g1 := cleanInvalid g
    if !(isValid g1 && isSegment g1 P) then return (1, r)
    let g2 := reviewParents g1
    if !(isValid g2 && isSegment g2 P) then return (2, r)
    let g3 := reviewSons g2
    if !(isValid g3 && isSegment g3 P) then return (3, r)
    if GPathM.measure g3 == GPathM.measure g then return (4, r)
    g := g3
  return (4, fuel)

def checkTT (lab : String) (T : GPathM) (e : Int × List NodeId) (a : TTAcc) : TTAcc := Id.run do
  let k := e.1
  let X := filterWeak T e
  let mut a := a
  for n in T.line (T.current_step - 1) do
    let (segs, _) := collectDown T [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        if low.id.step > k then
          let tabs := P.filterMap (fun y => (T.node? y).map (·.owners))
          let common := match tabs.head? with
            | none => []
            | some t0 => (ownersAt t0 k).filter (fun r => tabs.all (fun t => t.contains r))
          if !common.any (fun r => e.2.contains r.id) then
            a := { a with chains := a.chains + 1 }
            -- en X las tablas son las de T; la global de X ya está filtrada
            let indiv := tabs.any (fun t => !(ownersAt t k).any (fun r => e.2.contains r.id))
            let (st, rd) := stageOfDeath X P 40
            let st' := if st ≥ 4 then 0 else st
            if indiv then
              a := { a with indiv := a.indiv + 1, byStage := a.byStage.modify st' (· + 1) }
            else
              a := { a with helly := a.helly + 1, hellyLen := a.hellyLen + P.length
                          , hellyStage := a.hellyStage.modify st' (· + 1)
                          , hellyRound1 := a.hellyRound1 + (if rd == 0 then 1 else 0)
                          , examples := if a.examples.length < 3 then
                              a.examples ++ [s!"{lab} k={k} cadena {P.map (·.id.step)} etapa {st} vuelta {rd}"]
                            else a.examples }
  return a

partial def walkTT (lab : String) (g : GPathM) (fuel : Nat) (a : TTAcc) : TTAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := checkTT s!"{lab} pin" g (k, [q.id]) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkTT lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaTT (label : String) (φ : Cnf) (a : TTAcc) : TTAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        for e in es do
          if isValid T then
            a := checkTT s!"{label} envio paso {step}" T e a
            T := AggressiveReview.reviewAgg (filterWeak T e)
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkTT s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportTT (name : String) (a : TTAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   cadenas sin entrada comun admitida: {a.chains}"
  IO.println s!"   muerte individual (un miembro sin ninguna admitida): {a.indiv}  etapas [estado,clean,padres,hijos] {a.byStage}"
  IO.println s!"   caso Helly (cada uno tiene, ninguna comun): {a.helly}  (long. media {if a.helly == 0 then 0 else a.hellyLen / a.helly})"
  IO.println s!"     etapas [estado,clean,padres,hijos] {a.hellyStage}, en la primera vuelta {a.hellyRound1}"
  for ex in a.examples do IO.println s!"     ej: {ex}"
  IO.println s!"   ({ms} ms)"

/-! **`topmin`: ¿hay un miembro mínimo?** En estados revisados (estado de partida de cada filtro de un
paso del envío, y estados del lector), para cada cadena desde la cima `P` y cada paso `i` por debajo
de ella: (a) ¿algún miembro tiene su tabla en `i` dentro de la de todos? (b) ¿lo es el más bajo?
(c) lo mismo mirando solo ids de mapa. (h) ¿para todo id `x` presente en `i` en todas las tablas hay
una entrada común con ese id? -/

structure TMAcc where
  formulas : Nat := 0
  cases : Nat := 0
  anyMin : Nat := 0
  lowMin : Nat := 0
  anyMinId : Nat := 0
  idHelly : Nat := 0
  first : String := ""
  deriving Repr

def checkTM (lab : String) (g : GPathM) (a : TMAcc) : TMAcc := Id.run do
  if !isValid g then return a
  let mut a := a
  for n in g.line (g.current_step - 1) do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        let tabs := P.filterMap (fun y => (g.node? y).map (·.owners))
        for i in (intRange 0 (low.id.step - 1)) do
          let ats := tabs.map (fun t => ownersAt t i)
          let sub := fun (x y : List PathNodeId) => x.all (fun r => y.contains r)
          let subId := fun (x y : List PathNodeId) =>
            x.all (fun r : PathNodeId => y.any (fun r' : PathNodeId => r'.id == r.id))
          let am : Bool := ats.any (fun t => ats.all (fun t' => sub t t'))
          let lm : Bool := match ats.head? with | some t0 => ats.all (fun t' => sub t0 t') | none => true
          let ami : Bool := ats.any (fun t => ats.all (fun t' => subId t t'))
          let ids : List NodeId := match ats.head? with
            | some t0 => (t0.map (fun r : PathNodeId => r.id)).filter
                (fun x => ats.all (fun t : List PathNodeId => t.any (fun r => r.id == x)))
            | none => []
          let ih : Bool := ids.all (fun x => match ats.head? with
            | some t0 => (t0.filter (fun r : PathNodeId => r.id == x)).any
                (fun r => ats.all (fun t : List PathNodeId => t.contains r))
            | none => true)
          a := { a with cases := a.cases + 1, anyMin := a.anyMin + (if am then 1 else 0)
                      , lowMin := a.lowMin + (if lm then 1 else 0), anyMinId := a.anyMinId + (if ami then 1 else 0)
                      , idHelly := a.idHelly + (if ih then 1 else 0)
                      , first := if a.first == "" && !ih then s!"{lab} i={i} cadena {P.map (·.id.step)}" else a.first }
  return a

partial def walkTM (lab : String) (g : GPathM) (fuel : Nat) (a : TMAcc) : TMAcc :=
  let a := checkTM lab g a
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkTM lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaTM (label : String) (φ : Cnf) (a : TMAcc) : TMAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := checkTM s!"{label} linea+review paso {step}" (AggressiveReview.reviewAgg kv.2) a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkTM s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportTM (name : String) (a : TMAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   (cadena desde la cima, paso por debajo): {a.cases}"
  IO.println s!"     (a) hay miembro minimo: {a.anyMin}   (b) el mas bajo es minimo: {a.lowMin}"
  IO.println s!"     (c) minimo por ids: {a.anyMinId}   (h) Helly por id: {a.idHelly}"
  if a.first != "" then IO.println s!"   primer fallo de (h): {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`sandwich`: ¿la tabla colectiva es la intersección de dos tablas?** En estados revisados (línea
tras su review y estados del lector), cadenas desde la cima `P = c_lo … c_top`, y cada paso `i` por
debajo: (S1) `T_lo ∩ T_top` en `i` está en la tabla de todos; (S2) `T_lo ∩ T_{lo+1}`; (S3) hay alguna
pareja de miembros cuya intersección en `i` está en todas. -/

structure SWAcc where
  formulas : Nat := 0
  cases : Nat := 0
  s1 : Nat := 0
  s2 : Nat := 0
  s3 : Nat := 0
  withLo : Nat := 0
  withTop : Nat := 0
  singleOk : Nat := 0
  loWithSome : Array Nat := #[]
  first : String := ""
  deriving Repr

def checkSW (lab : String) (g : GPathM) (a : SWAcc) : SWAcc := Id.run do
  if !isValid g then return a
  let mut a := a
  for n in g.line (g.current_step - 1) do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        if P.length ≥ 3 then
          let tabs := P.filterMap (fun y => (g.node? y).map (·.owners))
          for i in (intRange 0 (low.id.step - 1)) do
            let ats : List (List PathNodeId) := tabs.map (fun t => ownersAt t i)
            let inAll : List PathNodeId → Bool := fun xs => xs.all (fun r => ats.all (fun t => t.contains r))
            let inter : List PathNodeId → List PathNodeId → List PathNodeId :=
              fun x y => x.filter (fun r => y.contains r)
            let t0 := ats.headD []
            let tl := ats.getLastD []
            let t1 := ats.getD 1 []
            let b1 : Bool := inAll (inter t0 tl)
            let b2 : Bool := inAll (inter t0 t1)
            let b3 : Bool := ats.any (fun x => ats.any (fun y => inAll (inter x y)))
            let bl : Bool := ats.any (fun y => inAll (inter t0 y))
            let bt : Bool := ats.any (fun y => inAll (inter tl y))
            let bs : Bool := ats.any (fun x => inAll x)
            -- con qué miembro (por distancia al más bajo) empareja el más bajo, la primera vez
            let idx := (List.range ats.length).find? (fun j => inAll (inter t0 (ats.getD j [])))
            a := { a with withLo := a.withLo + (if bl then 1 else 0), withTop := a.withTop + (if bt then 1 else 0)
                        , singleOk := a.singleOk + (if bs then 1 else 0) }
            match idx with
            | some j =>
              let arr := if a.loWithSome.size ≤ j then a.loWithSome ++ Array.replicate (j + 1 - a.loWithSome.size) 0 else a.loWithSome
              a := { a with loWithSome := arr.modify j (· + 1) }
            | none => pure ()
            a := { a with cases := a.cases + 1, s1 := a.s1 + (if b1 then 1 else 0)
                        , s2 := a.s2 + (if b2 then 1 else 0), s3 := a.s3 + (if b3 then 1 else 0)
                        , first := if a.first == "" && !b1 then s!"{lab} i={i} cadena {P.map (·.id.step)}" else a.first }
  return a

partial def walkSW (lab : String) (g : GPathM) (fuel : Nat) (a : SWAcc) : SWAcc :=
  let a := checkSW lab g a
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkSW lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaSW (label : String) (φ : Cnf) (a : SWAcc) : SWAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := checkSW s!"{label} linea+review paso {step}" (AggressiveReview.reviewAgg kv.2) a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkSW s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportSW (name : String) (a : SWAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   (cadena desde la cima de 3+, paso por debajo): {a.cases}"
  IO.println s!"     (S1) mas bajo y cima bastan: {a.s1}   (S2) mas bajo y siguiente: {a.s2}   (S3) alguna pareja: {a.s3}"
  IO.println s!"     alguna pareja con el mas bajo: {a.withLo}   con la cima: {a.withTop}   un solo miembro basta: {a.singleOk}"
  IO.println s!"     primer companero del mas bajo que basta (por distancia): {a.loWithSome}"
  if a.first != "" then IO.println s!"   primer fallo de S1: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`fusion`: ¿el ancla de la tabla colectiva es un nodo fusión?** Mismos casos que `sandwich`. Nodo
fusión = miembro con 2+ padres; bifurcación = 2+ hijos. Reglas: (F1) el fusión más bajo (si no hay,
el más bajo); (F2) el fusión más alto; (B1) la bifurcación más baja. Para cada regla: ¿su tabla sola
basta? ¿basta con el más bajo? Y: entre los miembros cuya tabla sola basta, ¿hay algún fusión? -/

structure FUAcc where
  formulas : Nat := 0
  cases : Nat := 0
  f1 : Nat := 0
  f1lo : Nat := 0
  f2 : Nat := 0
  f2lo : Nat := 0
  b1 : Nat := 0
  b1lo : Nat := 0
  anchorFusion : Nat := 0
  anchorAny : Nat := 0
  noFusion : Nat := 0
  deriving Repr

def checkFU (g : GPathM) (a : FUAcc) : FUAcc := Id.run do
  if !isValid g then return a
  let mut a := a
  for n in g.line (g.current_step - 1) do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        if P.length ≥ 3 then
          let nodes := P.filterMap (fun y => g.node? y)
          let fus : List Bool := nodes.map (fun m => decide (m.parents.length ≥ 2))
          let forks : List Bool := nodes.map (fun m => decide (m.sons.length ≥ 2))
          let pick : List Bool → Bool → Nat := fun fl lowest =>
            let idxs := (List.range fl.length).filter (fun j => fl.getD j false)
            if lowest then idxs.headD 0 else idxs.getLastD 0
          let jf1 := pick fus true
          let jf2 := pick fus false
          let jb1 := pick forks true
          let hasF : Bool := fus.any id
          for i in (intRange 0 (low.id.step - 1)) do
            let ats : List (List PathNodeId) := nodes.map (fun m => ownersAt m.owners i)
            let inAll : List PathNodeId → Bool := fun xs => xs.all (fun r => ats.all (fun t => t.contains r))
            let inter : List PathNodeId → List PathNodeId → List PathNodeId :=
              fun x y => x.filter (fun r => y.contains r)
            let t0 := ats.headD []
            let tj := fun (j : Nat) => ats.getD j []
            let anchors := (List.range ats.length).filter (fun j => inAll (tj j))
            a := { a with cases := a.cases + 1
                        , f1 := a.f1 + (if inAll (tj jf1) then 1 else 0)
                        , f1lo := a.f1lo + (if inAll (inter t0 (tj jf1)) then 1 else 0)
                        , f2 := a.f2 + (if inAll (tj jf2) then 1 else 0)
                        , f2lo := a.f2lo + (if inAll (inter t0 (tj jf2)) then 1 else 0)
                        , b1 := a.b1 + (if inAll (tj jb1) then 1 else 0)
                        , b1lo := a.b1lo + (if inAll (inter t0 (tj jb1)) then 1 else 0)
                        , anchorAny := a.anchorAny + (if anchors.isEmpty then 0 else 1)
                        , anchorFusion := a.anchorFusion + (if anchors.any (fun j => fus.getD j false) then 1 else 0)
                        , noFusion := a.noFusion + (if hasF then 0 else 1) }
  return a

partial def walkFU (g : GPathM) (fuel : Nat) (a : FUAcc) : FUAcc :=
  let a := checkFU g a
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkFU (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaFU (φ : Cnf) (a : FUAcc) : FUAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := checkFU (AggressiveReview.reviewAgg kv.2) a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkFU g (stepCount φ).toNat a
  return a

def reportFU (name : String) (a : FUAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   casos {a.cases} (cadenas sin ningun fusion: {a.noFusion})"
  IO.println s!"   (F1) fusion mas bajo solo: {a.f1}   con el mas bajo: {a.f1lo}"
  IO.println s!"   (F2) fusion mas alto solo: {a.f2}   con el mas bajo: {a.f2lo}"
  IO.println s!"   (B1) bifurcacion mas baja sola: {a.b1}   con el mas bajo: {a.b1lo}"
  IO.println s!"   hay ancla sola: {a.anchorAny}   y es un fusion: {a.anchorFusion}"
  IO.println s!"   ({ms} ms)"

/-! **`fusrow`: ¿el ancla es el miembro del paso de fusión?** Mismos casos que `sandwich`, con
`F = litBlock φ` (el `FusionNode` que separa literales de cláusulas). Para cadenas que pasan por `F`
(`lo ≤ F`): ¿la tabla del miembro en `F` basta sola? ¿con el más bajo? Separado por `i < F` / `i > F`.
Y para cadenas por encima de `F`: ¿basta la tabla del más bajo? -/

structure FRAcc where
  formulas : Nat := 0
  thruBelow : Nat := 0
  thruBelowOk : Nat := 0
  thruBelowLo : Nat := 0
  thruAbove : Nat := 0
  thruAboveOk : Nat := 0
  thruAboveLo : Nat := 0
  over : Nat := 0
  overLow : Nat := 0
  overAny : Nat := 0
  deriving Repr

def checkFR (F : Int) (g : GPathM) (a : FRAcc) : FRAcc := Id.run do
  if !isValid g then return a
  let mut a := a
  for n in g.line (g.current_step - 1) do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        if P.length ≥ 3 then
          let nodes := P.filterMap (fun y => g.node? y)
          let jF := (List.range P.length).find? (fun j => ((P.getD j low).id.step == F))
          for i in (intRange 0 (low.id.step - 1)) do
            let ats : List (List PathNodeId) := nodes.map (fun m => ownersAt m.owners i)
            let inAll : List PathNodeId → Bool := fun xs => xs.all (fun r => ats.all (fun t => t.contains r))
            let inter : List PathNodeId → List PathNodeId → List PathNodeId :=
              fun x y => x.filter (fun r => y.contains r)
            let t0 := ats.headD []
            match jF with
            | some j =>
              let tF := ats.getD j []
              let ok : Bool := inAll tF
              let okLo : Bool := inAll (inter t0 tF)
              if i < F then
                a := { a with thruBelow := a.thruBelow + 1, thruBelowOk := a.thruBelowOk + (if ok then 1 else 0)
                            , thruBelowLo := a.thruBelowLo + (if okLo then 1 else 0) }
              else
                a := { a with thruAbove := a.thruAbove + 1, thruAboveOk := a.thruAboveOk + (if ok then 1 else 0)
                            , thruAboveLo := a.thruAboveLo + (if okLo then 1 else 0) }
            | none =>
              if low.id.step > F then
                let anyA : Bool := ats.any (fun t => inAll t)
                a := { a with over := a.over + 1, overLow := a.overLow + (if inAll t0 then 1 else 0)
                            , overAny := a.overAny + (if anyA then 1 else 0) }
  return a

partial def walkFR (F : Int) (g : GPathM) (fuel : Nat) (a : FRAcc) : FRAcc :=
  let a := checkFR F g a
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkFR F (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaFR (φ : Cnf) (a : FRAcc) : FRAcc := Id.run do
  let F := litBlock φ
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := checkFR F (AggressiveReview.reviewAgg kv.2) a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkFR F g (stepCount φ).toNat a
  return a

def reportFR (name : String) (a : FRAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   cadenas por F, paso i < F: {a.thruBelow}   tabla de F sola: {a.thruBelowOk}   F con el mas bajo: {a.thruBelowLo}"
  IO.println s!"   cadenas por F, paso i > F: {a.thruAbove}   tabla de F sola: {a.thruAboveOk}   F con el mas bajo: {a.thruAboveLo}"
  IO.println s!"   cadenas por encima de F: {a.over}   el mas bajo solo: {a.overLow}   algun ancla: {a.overAny}"
  IO.println s!"   ({ms} ms)"

/-! **`anchordist`: ¿a qué distancia del paso `i` está el ancla?** Mismos casos que `sandwich`. Para
cada caso: distancia `paso − i` del miembro más cercano a `i` cuya tabla sola basta (si lo hay), y del
más lejano; y si ninguno basta solo, la mejor pareja (la de menor distancia máxima a `i`). También:
¿basta el miembro más cercano a `i`, el más bajo de la cadena? ¿basta el más alto (la cima)? -/

structure ADAcc where
  formulas : Nat := 0
  cases : Nat := 0
  nearest : Array Nat := #[]
  farthest : Array Nat := #[]
  pairOnly : Array Nat := #[]
  lowOk : Nat := 0
  topOk : Nat := 0
  allAnchors : Nat := 0
  lowOrTop : Nat := 0
  lowTopPair : Nat := 0
  deriving Repr

def bumpAD (arr : Array Nat) (j : Nat) : Array Nat :=
  let arr := if arr.size ≤ j then arr ++ Array.replicate (j + 1 - arr.size) 0 else arr
  arr.modify j (· + 1)

def checkAD (g : GPathM) (a : ADAcc) : ADAcc := Id.run do
  if !isValid g then return a
  let mut a := a
  for n in g.line (g.current_step - 1) do
    let (segs, _) := collectDown g [n.id] ([], 60)
    for P in segs do
      match P.head? with
      | none => pure ()
      | some low =>
        if P.length ≥ 3 then
          let nodes := P.filterMap (fun y => g.node? y)
          for i in (intRange 0 (low.id.step - 1)) do
            let ats : List (List PathNodeId) := nodes.map (fun m => ownersAt m.owners i)
            let inAll : List PathNodeId → Bool := fun xs => xs.all (fun r => ats.all (fun t => t.contains r))
            let inter : List PathNodeId → List PathNodeId → List PathNodeId :=
              fun x y => x.filter (fun r => y.contains r)
            let dist : Nat → Nat := fun j => ((P.getD j low).id.step - i).toNat
            let anchors := (List.range ats.length).filter (fun j => inAll (ats.getD j []))
            a := { a with cases := a.cases + 1
                        , lowOk := a.lowOk + (if inAll (ats.headD []) then 1 else 0)
                        , topOk := a.topOk + (if inAll (ats.getLastD []) then 1 else 0)
                        , allAnchors := a.allAnchors + (if anchors.length == ats.length then 1 else 0)
                        , lowOrTop := a.lowOrTop + (if inAll (ats.headD []) || inAll (ats.getLastD []) then 1 else 0)
                        , lowTopPair := a.lowTopPair + (if inAll (inter (ats.headD []) (ats.getLastD [])) then 1 else 0) }
            match anchors.head?, anchors.getLast? with
            | some j0, some j1 =>
              a := { a with nearest := bumpAD a.nearest (dist j0), farthest := bumpAD a.farthest (dist j1) }
            | _, _ =>
              let rng := List.range ats.length
              let best := rng.foldl (fun (acc : Option Nat) x => rng.foldl (fun acc y =>
                if inAll (inter (ats.getD x []) (ats.getD y [])) then
                  let m := max (dist x) (dist y)
                  match acc with | some b => some (min b m) | none => some m
                else acc) acc) none
              match best with
              | some m => a := { a with pairOnly := bumpAD a.pairOnly m }
              | none => pure ()
  return a

partial def walkAD (g : GPathM) (fuel : Nat) (a : ADAcc) : ADAcc :=
  let a := checkAD g a
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k =>
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => a
      | some q => walkAD (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaAD (φ : Cnf) (a : ADAcc) : ADAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := checkAD (AggressiveReview.reviewAgg kv.2) a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkAD g (stepCount φ).toNat a
  return a

def reportAD (name : String) (a : ADAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.cases} casos)"
  IO.println s!"   el mas bajo basta: {a.lowOk}   la cima basta: {a.topOk}   todos bastan: {a.allAnchors}"
  IO.println s!"   el mas bajo o la cima: {a.lowOrTop}   la pareja (mas bajo, cima): {a.lowTopPair}"
  IO.println s!"   ancla mas cercana a i, por distancia (paso - i): {a.nearest}"
  IO.println s!"   ancla mas lejana a i, por distancia: {a.farthest}"
  IO.println s!"   sin ancla sola, mejor pareja por distancia maxima: {a.pairOnly}"
  IO.println s!"   ({ms} ms)"

/-! **`passhyp`: las hipótesis de `segGood_reviewNode_parents/sons` tal como están enunciadas**, en el
estado de antes de cada `reviewNode` de las pasadas de padres y de hijos: (I1) toda entrada de la
tabla un paso por debajo es padre —también ids muertos—; lo mismo solo para vivos; (I1-hijos) por
encima; padres vivos; hijos vivos; cada nodo vivo se posee. Se cuentan estados que violan. -/

structure PHCell where
  states : Nat := 0
  i1all : Nat := 0
  i1live : Nat := 0
  i1sall : Nat := 0
  i1slive : Nat := 0
  plive : Nat := 0
  slive : Nat := 0
  self : Nat := 0
  segs : Nat := 0
  segDead : Nat := 0
  segNone : Nat := 0
  removed : Nat := 0
  removedSole : Nat := 0
  deriving Repr

/-- ¿Es `x` la única entrada común viva, en su paso, de algún tramo que no lo contiene? -/
def soleLiveCommon (g : GPathM) (x : PathNodeId) : Bool := Id.run do
  for y in g.nodes.take 20 do
    let (segs, _) := collectDown g [y.id] ([], 30)
    for P in segs do
      match P.head?, P.getLast? with
      | some lo, some hi =>
        let i := x.id.step
        if i < lo.id.step || hi.id.step < i then
          let tabs := P.filterMap (fun z => (g.node? z).map (·.owners))
          let common := (ownersAt (tabs.headD []) i).filter (fun r => tabs.all (fun t => t.contains r))
          let live := common.filter (fun r => (g.node? r).isSome)
          if live == [x] then return true
      | _, _ => pure ()
  return false

/-- `SegGood` en versión viva: para cada tramo y cada paso fuera, ¿hay entrada común? ¿viva? -/
def segLiveCheck (g : GPathM) : Nat × Nat × Nat := Id.run do
  let mut n := 0
  let mut dead := 0
  let mut none := 0
  for x in g.nodes.take 20 do
    let (segs, _) := collectDown g [x.id] ([], 30)
    for P in segs do
      match P.head?, P.getLast? with
      | some lo, some hi =>
        let tabs := P.filterMap (fun y => (g.node? y).map (·.owners))
        for i in intRange 0 (g.current_step - 1) do
          if i < lo.id.step || hi.id.step < i then
            n := n + 1
            let common := (ownersAt (tabs.headD []) i).filter (fun r => tabs.all (fun t => t.contains r))
            if common.isEmpty then none := none + 1
            else if !common.any (fun r => (g.node? r).isSome) then dead := dead + 1
      | _, _ => pure ()
  return (n, dead, none)

def checkPH (g : GPathM) (c : PHCell) : PHCell := Id.run do
  if !isValid g then return c
  let mut a1 := false
  let mut a1l := false
  let mut a2 := false
  let mut a2l := false
  let mut pl := false
  let mut sl := false
  let mut sf := false
  for n in g.nodes do
    if !n.owners.contains n.id then sf := true
    for p in n.parents do
      if (g.node? p).isNone then pl := true
    for q in n.sons do
      if (g.node? q).isNone then sl := true
    for w in n.owners do
      let live := (g.node? w).isSome
      if w.id.step + 1 == n.id.id.step && !n.parents.contains w then
        a1 := true
        if live then a1l := true
      if w.id.step == n.id.id.step + 1 && !n.sons.contains w then
        a2 := true
        if live then a2l := true
  let (ns, nd, nn) := segLiveCheck g
  return { states := c.states + 1, segs := c.segs + ns, segDead := c.segDead + nd, segNone := c.segNone + nn
         , i1all := c.i1all + (if a1 then 1 else 0), i1live := c.i1live + (if a1l then 1 else 0)
         , i1sall := c.i1sall + (if a2 then 1 else 0), i1slive := c.i1slive + (if a2l then 1 else 0)
         , plive := c.plive + (if pl then 1 else 0), slive := c.slive + (if sl then 1 else 0)
         , self := c.self + (if sf then 1 else 0) }

structure PHAcc where
  formulas : Nat := 0
  par : PHCell := {}
  sons : PHCell := {}
  deriving Repr

def instrStepsPH (g0 : GPathM) (nb : PNodeM → List PathNodeId) (ks : List Int) (c0 : PHCell) :
    GPathM × PHCell := Id.run do
  let mut g := g0
  let mut c := c0
  for k in ks do
    if !isValid g then return (g, c)
    for id in (g.line k).map (·.id) do
      c := checkPH g c
      let g' := reviewNode g nb id
      if (g'.node? id).isNone && (g.node? id).isSome then
        c := { c with removed := c.removed + 1, removedSole := c.removedSole + (if soleLiveCommon g id then 1 else 0) }
      g := g'
  return (g, c)

def reviewPH (F : GPathM) (a : PHAcc) : PHAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut fuel := GPathM.measure g + 1
  while fuel > 0 do
    fuel := fuel - 1
    if !isValid g then fuel := 0
    else
      let g0 := g
      let h := cleanInvalid g
      let (h2, cp) := instrStepsPH h (·.parents) (intRange 1 (h.current_step - 1)) a.par
      a := { a with par := cp }
      let (h3, cs) := instrStepsPH h2 (·.sons) (intRange 0 (h2.current_step - 2)).reverse a.sons
      a := { a with sons := cs }
      g := h3
      if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
  return a

def runFormulaPH (φ : Cnf) (a : PHAcc) : PHAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewPH F a
    line := pureAdvanceW φ line
  return a

def reportPHCell (lbl : String) (c : PHCell) : IO Unit := do
  IO.println s!"   {lbl}: estados {c.states}; violan I1 {c.i1all} (vivos {c.i1live}), I1-hijos {c.i1sall} (vivos {c.i1slive}), padres vivos {c.plive}, hijos vivos {c.slive}, self {c.self}"
  IO.println s!"      SegGood: casos {c.segs}, sin entrada comun {c.segNone}, solo entradas muertas {c.segDead}"
  IO.println s!"      nodos eliminados {c.removed}, de ellos unica entrada comun viva de algun tramo {c.removedSole}"

def reportPH (name : String) (a : PHAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportPHCell "pasada de padres" a.par
  reportPHCell "pasada de hijos " a.sons
  IO.println s!"   ({ms} ms)"

/-! **`cleanpass`: qué deja en pie `cleanInvalid` a pasada entera.** En cada vuelta del review de cada
envío y de cada pin del lector: las condiciones de `PState` (I1 vivos, I1-hijos vivos, padres e hijos
vivos, autoposesión, `SegGood` con entrada viva) en el estado de ENTRADA de `cleanInvalid` y en el de
SALIDA. -/

structure CPAcc where
  formulas : Nat := 0
  input : PHCell := {}
  output : PHCell := {}
  rinput : PHCell := {}
  routput : PHCell := {}
  deriving Repr

def reviewCP (F : GPathM) (a : CPAcc) : CPAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut fuel := GPathM.measure g + 1
  while fuel > 0 do
    fuel := fuel - 1
    if !isValid g then fuel := 0
    else
      let g0 := g
      a := { a with input := checkPH g a.input }
      let h := cleanInvalid g
      if isValid h then a := { a with output := checkPH h a.output }
      let h3 := reviewSons (reviewParents h)
      g := h3
      if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
  return a

def merged (x y : PHCell) : PHCell :=
  { states := x.states + y.states, i1all := x.i1all + y.i1all, i1live := x.i1live + y.i1live
  , i1sall := x.i1sall + y.i1sall, i1slive := x.i1slive + y.i1slive, plive := x.plive + y.plive
  , slive := x.slive + y.slive, self := x.self + y.self, segs := x.segs + y.segs
  , segDead := x.segDead + y.segDead, segNone := x.segNone + y.segNone
  , removed := x.removed + y.removed, removedSole := x.removedSole + y.removedSole }

partial def walkCP (g : GPathM) (fuel : Nat) (a : CPAcc) : CPAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        let b := reviewCP ([q.id].foldl filterRequire g) { a with input := {}, output := {} }
        a := { a with rinput := merged a.rinput b.input, routput := merged a.routput b.output }
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkCP (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaCP (φ : Cnf) (a : CPAcc) : CPAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewCP F a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkCP g (stepCount φ).toNat a
  return a

def reportCP (name : String) (a : CPAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportPHCell "ENVIOS entrada de cleanInvalid" a.input
  reportPHCell "ENVIOS salida de cleanInvalid " a.output
  reportPHCell "PINES entrada de cleanInvalid" a.rinput
  reportPHCell "PINES salida de cleanInvalid " a.routput
  IO.println s!"   ({ms} ms)"

/-! **`doomed`: los tramos que `cleanInvalid` deja sin entrada común viva, ¿mueren?** En los pines del
lector (y en los envíos), tras cada `cleanInvalid` de cada vuelta: para cada tramo que viola
`SegGoodL` (algún paso fuera sin entrada común viva), ¿sigue siendo tramo tras el review completo
(`reviewAgg` del filtrado)? ¿y tras la pasada de padres e hijos de esa misma vuelta? -/

structure DMAcc where
  formulas : Nat := 0
  bad : Nat := 0
  badDieRound : Nat := 0
  badDieFinal : Nat := 0
  badSurvive : Nat := 0
  first : String := ""
  deriving Repr

def badSegs (g : GPathM) : List (List PathNodeId) := Id.run do
  let mut out : List (List PathNodeId) := []
  for x in g.nodes.take 20 do
    let (segs, _) := collectDown g [x.id] ([], 30)
    for P in segs do
      match P.head?, P.getLast? with
      | some lo, some hi =>
        let tabs := P.filterMap (fun y => (g.node? y).map (·.owners))
        let mut bad := false
        for i in intRange 0 (g.current_step - 1) do
          if i < lo.id.step || hi.id.step < i then
            let common := (ownersAt (tabs.headD []) i).filter (fun r => tabs.all (fun t => t.contains r))
            if !common.any (fun r => (g.node? r).isSome) then bad := true
        if bad then out := P :: out
      | _, _ => pure ()
  return out

def reviewDM (lab : String) (F : GPathM) (a : DMAcc) : DMAcc := Id.run do
  let R := AggressiveReview.reviewAgg F
  let mut a := a
  let mut g := F
  let mut fuel := GPathM.measure g + 1
  while fuel > 0 do
    fuel := fuel - 1
    if !isValid g then fuel := 0
    else
      let g0 := g
      let h := cleanInvalid g
      let h3 := reviewSons (reviewParents h)
      if isValid h then
        for P in badSegs h do
          let dieRound := !(isValid h3 && isSegment h3 P)
          let dieFinal := !(isValid R && isSegment R P)
          a := { a with bad := a.bad + 1, badDieRound := a.badDieRound + (if dieRound then 1 else 0)
                      , badDieFinal := a.badDieFinal + (if dieFinal then 1 else 0)
                      , badSurvive := a.badSurvive + (if dieFinal then 0 else 1)
                      , first := if a.first == "" && !dieFinal then s!"{lab} tramo {P.map (·.id.step)}" else a.first }
      g := h3
      if !(GPathM.measure h3 < GPathM.measure g0) then fuel := 0
  return a

partial def walkDM (lab : String) (g : GPathM) (fuel : Nat) (a : DMAcc) : DMAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := reviewDM lab ([q.id].foldl filterRequire g) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkDM lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaDM (label : String) (φ : Cnf) (a : DMAcc) : DMAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  for kv in pureRunW φ do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkDM s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportDM (name : String) (a : DMAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   tramos sin entrada comun viva tras cleanInvalid (pines del lector): {a.bad}"
  IO.println s!"     mueren en esa misma vuelta (padres + hijos): {a.badDieRound}   mueren al final del review: {a.badDieFinal}   SOBREVIVEN: {a.badSurvive}"
  if a.first != "" then IO.println s!"   primero que sobrevive: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`filterkillcs`: la completitud en la forma `ChainSound`.** Como `filterkill`, pero la extensión
tiene que ser `ChainSound`: cada miembro se posee, el enlace se ve desde los dos lados (padre en el
hijo, hijo en el padre) y la raíz está en el paso 0 y solo allí. -/

def csNodeOk (g : GPathM) (r : PathNodeId) : Bool :=
  match g.node? r with
  | none => false
  | some n => n.owners.contains r &&
      (if r.id.step == 0 then r.parent_id.isNone else r.parent_id.isSome)

def csLinked (g : GPathM) (lo hi : PathNodeId) : Bool :=
  (match g.node? hi with | some n => n.parents.contains lo | none => false) &&
  (match g.node? lo with | some n => n.sons.contains hi | none => false)

partial def extendCS (g : GPathM) (ok : PathNodeId → Bool) (P : List PathNodeId) (budget : Nat) :
    Option Bool × Nat :=
  if budget == 0 then (none, 0)
  else
    match P.head?, P.getLast? with
    | some low, some high =>
      let step (cands : List PathNodeId) (mk : PathNodeId → List PathNodeId) : Option Bool × Nat :=
        cands.foldl (fun (acc : Option Bool × Nat) r =>
          match acc with
          | (some true, b) => (some true, b)
          | (res, b) =>
            if b == 0 then (none, 0)
            else
              let (r', b') := extendCS g ok (mk r) (b - 1)
              match r', res with
              | some true, _ => (some true, b')
              | none, _ => (none, b')
              | some false, none => (none, b')
              | some false, _ => (some false, b'))
          (some false, budget)
      if low.id.step > 0 then
        let cands := match g.node? low with
          | some n => n.parents.filter (fun r => ok r && fitsAll g P r && csNodeOk g r && csLinked g r low)
          | none => []
        step cands (fun r => r :: P)
      else if high.id.step < g.current_step - 1 then
        let cands := match g.node? high with
          | some n => n.sons.filter (fun r => ok r && fitsAll g P r && csNodeOk g r && csLinked g high r)
          | none => []
        step cands (fun r => P ++ [r])
      else (some true, budget)
    | _, _ => (some true, budget)

structure FKCAcc where
  formulas : Nat := 0
  states : Nat := 0
  segs : Nat := 0
  segCS : Nat := 0        -- tramos cuyos propios miembros ya cumplen la forma ChainSound
  plainExt : Nat := 0
  csExt : Nat := 0
  csExtSurv : Nat := 0
  plainNotCs : Nat := 0   -- se extiende, pero no en forma ChainSound
  noExtSurv : Nat := 0    -- sobreviven sin extensión ChainSound
  first : String := ""
  deriving Repr

def checkFKC (lab : String) (F : GPathM) (cap budget : Nat) (a : FKCAcc) : FKCAcc := Id.run do
  let R := AggressiveReview.reviewAgg F
  let mut a := { a with states := a.states + 1 }
  let gow := F.gowners
  for n in F.nodes.take cap do
    if gow.contains n.id then
      let (segs, _) := collectDown F [n.id] ([], 60)
      for P in segs do
        if P.all (fun x => gow.contains x) then
          a := { a with segs := a.segs + 1 }
          let own := P.all (fun x => csNodeOk F x) &&
            (List.range (P.length - 1)).all (fun k =>
              match P[k]?, P[k + 1]? with
              | some x, some y => csLinked F x y
              | _, _ => false)
          if own then a := { a with segCS := a.segCS + 1 }
          let surv := isValid R && isSegment R P
          let pe := (extendFullIn F (fun r => gow.contains r) P budget).1 == some true
          let ce := own && (extendCS F (fun r => gow.contains r) P budget).1 == some true
          a := { a with plainExt := a.plainExt + (if pe then 1 else 0)
                      , csExt := a.csExt + (if ce then 1 else 0)
                      , csExtSurv := a.csExtSurv + (if ce && surv then 1 else 0)
                      , plainNotCs := a.plainNotCs + (if pe && !ce then 1 else 0)
                      , noExtSurv := a.noExtSurv + (if !ce && surv then 1 else 0)
                      , first := if a.first == "" && !ce && surv then
                          s!"{lab} tramo {P.map (·.id.step)} forma={own} ext={pe}" else a.first }
  return a

partial def walkFKC (lab : String) (g : GPathM) (fuel cap budget : Nat) (a : FKCAcc) : FKCAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := checkFKC s!"{lab} pin" ([q.id].foldl filterRequire g) cap budget a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkFKC lab (filterAllAgg g [q.id]) (fuel - 1) cap budget a

def runFormulaFKC (label : String) (φ : Cnf) (cap budget : Nat) (a : FKCAcc) : FKCAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := checkFKC s!"{label} paso {step} ⟨{kv.1.step},{kv.1.index}⟩→⟨{d.step},{d.index}⟩" F cap budget a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkFKC s!"{label} lector" g (stepCount φ).toNat cap budget a
  return a

def reportFKC (name : String) (a : FKCAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas, {a.states} estados filtrados)"
  IO.println s!"   tramos dentro de la global: {a.segs} (sus miembros ya en forma ChainSound: {a.segCS})"
  IO.println s!"   se extienden (forma simple)        : {a.plainExt}"
  IO.println s!"   se extienden en forma ChainSound   : {a.csExt}  (sobreviven al review: {a.csExtSurv})"
  IO.println s!"   simple SI pero ChainSound NO       : {a.plainNotCs}"
  IO.println s!"   SOBREVIVEN sin extension ChainSound: {a.noExtSurv}"
  if a.first != "" then IO.println s!"   primero: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`clean2`: el `cleanInvalid` en dos fases frente al actual** (v181 §6, paso 6.0). En cada envío y
en cada pin del lector: ¿dejan `reviewAgg` y `reviewAgg₂` el mismo estado (validez, global, nodos con
tablas, padres e hijos, como conjuntos)? Y tras cada `cleanInvalid₂` de cada vuelta de `review₂`: las
postcondiciones (tablas dentro de la global, global = nodos, nodos válidos, enlaces mutuos y dentro de
las tablas) y las condiciones de `PState` con ids muertos incluidos (`checkPH`). -/

/-- The sequential review, as it was before 2026-09-23 (`cleanInvalid` node by node), kept here only
so that `clean2` can compare the machine against it. -/
def reviewPassSeq (g : GPathM) : GPathM := reviewSons (reviewParents (cleanInvalid g))

def reviewFuelSeq : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := reviewPassSeq g
      if GPathM.measure g' < GPathM.measure g then reviewFuelSeq fuel g' else g'
    else g

def reviewSeq (g : GPathM) : GPathM := reviewFuelSeq (GPathM.measure g + 1) g

def reviewAggFuelSeq : Nat → GPathM → GPathM
  | 0, g => reviewSeq g
  | fuel + 1, g =>
    let g₁ := reviewSeq g
    if isValid g₁ then
      let g₂ := AggressiveReview.aggSweep g₁
      if GPathM.measure g₂ < GPathM.measure g₁ then reviewAggFuelSeq fuel g₂ else g₁
    else g₁

def reviewAggSeq (g : GPathM) : GPathM := reviewAggFuelSeq (GPathM.measure g + 1) g

structure C2Acc where
  formulas : Nat := 0
  sends : Nat := 0
  sendsDiff : Nat := 0
  pins : Nat := 0
  pinsDiff : Nat := 0
  validDiff : Nat := 0
  cleans : Nat := 0
  tableOut : Nat := 0
  globalNotNode : Nat := 0
  invalidNode : Nat := 0
  linkBad : Nat := 0
  ph : PHCell := {}
  first : String := ""
  deriving Repr

def setEqIds (a b : List PathNodeId) : Bool :=
  a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

def sameState2 (g h : GPathM) : Bool :=
  isValid g == isValid h &&
  (!isValid g ||
    (setEqIds g.gowners h.gowners && g.nodes.length == h.nodes.length &&
     g.nodes.all (fun n => match h.node? n.id with
       | some m => setEqIds n.owners m.owners && setEqIds n.parents m.parents && setEqIds n.sons m.sons
       | none => false)))

def post2 (h : GPathM) (a : C2Acc) : C2Acc := Id.run do
  if !isValid h then return a
  let mut a := { a with cleans := a.cleans + 1, ph := checkPH h a.ph }
  if h.nodes.any (fun n => n.owners.any (fun q => !h.gowners.contains q)) then
    a := { a with tableOut := a.tableOut + 1 }
  if h.gowners.any (fun q => (h.node? q).isNone) then
    a := { a with globalNotNode := a.globalNotNode + 1 }
  if h.nodes.any (fun n => !isValidNode h n) then
    a := { a with invalidNode := a.invalidNode + 1 }
  let mutualOk (n : PNodeM) (y : PathNodeId) : Bool :=
    n.owners.contains y && (match h.node? y with | some m => m.owners.contains n.id | none => false)
  let parentOk (n : PNodeM) (p : PathNodeId) : Bool :=
    mutualOk n p && (match h.node? p with | some m => m.sons.contains n.id | none => false)
  let sonOk (n : PNodeM) (s : PathNodeId) : Bool :=
    mutualOk n s && (match h.node? s with | some m => m.parents.contains n.id | none => false)
  if h.nodes.any (fun n => !(n.parents.all (parentOk n) && n.sons.all (sonOk n))) then
    a := { a with linkBad := a.linkBad + 1 }
  return a

/-- `review₂` instrumented: the postconditions after every `cleanInvalid₂`. -/
def review2Post (F : GPathM) (a : C2Acc) : C2Acc := Id.run do
  let mut a := a
  let mut g := F
  let mut fuel := GPathM.measure g + 1
  while fuel > 0 do
    fuel := fuel - 1
    if !isValid g then fuel := 0
    else
      let g0 := g
      let h := cleanInvalid₂ g
      a := post2 h a
      g := reviewSons (reviewParents h)
      if !(GPathM.measure g < GPathM.measure g0) then fuel := 0
  return a

def compare2 (lab : String) (pin : Bool) (F : GPathM) (a : C2Acc) : C2Acc := Id.run do
  let R := reviewAggSeq F
  let R₂ := AggressiveReview.reviewAgg F
  let same := sameState2 R R₂
  let mut a := review2Post F a
  if pin then a := { a with pins := a.pins + 1, pinsDiff := a.pinsDiff + (if same then 0 else 1) }
  else a := { a with sends := a.sends + 1, sendsDiff := a.sendsDiff + (if same then 0 else 1) }
  if isValid R != isValid R₂ then a := { a with validDiff := a.validDiff + 1 }
  if !same && a.first == "" then
    a := { a with first := s!"{lab} ({if pin then "pin" else "envio"}): valido {isValid R}/{isValid R₂}, nodos {R.nodes.length}/{R₂.nodes.length}, global {R.gowners.length}/{R₂.gowners.length}" }
  return a

partial def walkC2 (lab : String) (g : GPathM) (fuel : Nat) (a : C2Acc) : C2Acc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := compare2 lab true ([q.id].foldl filterRequire g) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkC2 lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaC2 (lab : String) (φ : Cnf) (a : C2Acc) : C2Acc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := compare2 lab false F a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkC2 lab g (stepCount φ).toNat a
  return a

def reportC2 (name : String) (a : C2Acc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   reviewAgg secuencial vs dos fases (la maquina): envios {a.sends} (distintos {a.sendsDiff}), pines {a.pins} (distintos {a.pinsDiff}), validez distinta {a.validDiff}"
  IO.println s!"   tras cleanInvalid₂ ({a.cleans} estados validos): tabla fuera de la global {a.tableOut}, global sin nodo {a.globalNotNode}, nodo invalido {a.invalidNode}, enlace no mutuo {a.linkBad}"
  reportPHCell "PState con ids muertos, tras cleanInvalid₂" a.ph
  if a.first != "" then IO.println s!"   primer distinto: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`minnode`: ¿es la tabla del nodo con menos owners un punto fijo?** (idea del autor, 2026-09-23:
`ReaderMinOwner`). En cada estado que visita el lector (la línea final tras `reviewAgg`, y cada pin,
hermanos incluidos) se toma `m`, el nodo con menos owners, y su tabla `T`:

* (sym) todo `w ∈ T` tiene a `m` en su tabla;
* (a) `T ⊆ tabla de w` para todo `w ∈ T` — que todo miembro posea a todo miembro (`Survive.Woven.own`);
* (b) `Survive.Closed` sobre `T`: miembros en la global y nodos; en cada paso cada miembro posee un
  miembro; un miembro no raíz tiene un padre miembro; uno no último es padre de un miembro; los
  enlazados se poseen;
* (c) restringir la global a `T` y aplicar `reviewAgg`: ¿válido? ¿sigue `T` entera en la global?
* (d) pasos con más de un owner en `T` (0 = el camino ya está resuelto);
* (any) ¿cumple (a) algún nodo del estado, aunque no sea el mínimo? -/

structure MNAcc where
  formulas : Nat := 0
  states : Nat := 0
  symFail : Nat := 0
  aFail : Nat := 0
  aPairs : Nat := 0
  aPairsFail : Nat := 0
  closedFail : Nat := 0
  wovenOk : Nat := 0
  restrictValid : Nat := 0
  restrictKeepsT : Nat := 0
  solved : Nat := 0
  multiSteps : Nat := 0
  anyA : Nat := 0
  anyWoven : Nat := 0
  tSize : Nat := 0
  apFail : Nat := 0
  apPairsFail : Nat := 0
  dupTables : Nat := 0
  picks : Nat := 0
  pickClosedFail : Nat := 0
  pickValid : Nat := 0
  pickKeeps : Nat := 0
  first : String := ""
  firstP : String := ""
  deriving Repr

def tableOf (G : GPathM) (p : PathNodeId) : List PathNodeId :=
  match G.node? p with | some n => n.owners | none => []

/-- (a) for a node `x`: every member of its table owns the whole table. -/
def ownsAll (G : GPathM) (T : List PathNodeId) : Bool :=
  T.all (fun w => T.all (fun v => (tableOf G w).contains v))

/-- (b) `Survive.Closed` for the set `T`. -/
def closedOn (G : GPathM) (T : List PathNodeId) : Bool :=
  let inT := fun (q : PathNodeId) => T.contains q
  T.all (fun p =>
    G.gowners.contains p &&
    (match G.node? p with
     | none => false
     | some n =>
       (intRange 0 (G.current_step - 1)).all (fun l => n.owners.any (fun v => inT v && v.id.step == l)) &&
       (p.parent_id.isNone || n.parents.any inT) &&
       (p.id.step == G.current_step - 1 ||
         T.any (fun c => match G.node? c with | some m => m.parents.contains p | none => false)) &&
       n.parents.all (fun c => !inT c ||
         (n.owners.contains c && (tableOf G c).contains p))))

def measureMN (lab : String) (G : GPathM) (a : MNAcc) : MNAcc := Id.run do
  if !isValid G then return a
  match G.nodes.head? with
  | none => return a
  | some n0 =>
  let m := G.nodes.foldl (fun b n => if n.owners.length < b.owners.length then n else b) n0
  let T := m.owners.eraseDups
  let mut a := { a with states := a.states + 1, tSize := a.tSize + T.length }
  if T.length != m.owners.length then a := { a with dupTables := a.dupTables + 1 }
  if !T.all (fun w => (tableOf G w).contains m.id) then a := { a with symFail := a.symFail + 1 }
  let pairs := T.length * T.length
  let bad := (T.map (fun w => (T.filter (fun v => !(tableOf G w).contains v)).length)).sum
  a := { a with aPairs := a.aPairs + pairs, aPairsFail := a.aPairsFail + bad }
  let aok := bad == 0
  if !aok then a := { a with aFail := a.aFail + 1 }
  let cok := closedOn G T
  if !cok then a := { a with closedFail := a.closedFail + 1 }
  if aok && cok then a := { a with wovenOk := a.wovenOk + 1 }
  let G' : GPathM := { G with gowners := G.gowners.filter (fun q => T.contains q) }
  let R := AggressiveReview.reviewAgg G'
  if isValid R then
    a := { a with restrictValid := a.restrictValid + 1 }
    if T.all (fun q => R.gowners.contains q) then a := { a with restrictKeepsT := a.restrictKeepsT + 1 }
  let multi := ((intRange 0 (G.current_step - 1)).filter
    (fun l => (T.filter (fun q => q.id.step == l)).length > 1)).length
  if multi == 0 then a := { a with solved := a.solved + 1 }
  a := { a with multiSteps := a.multiSteps + multi }
  -- (a') relative to the step: T without w's siblings is inside w's table
  let sib := fun (w v : PathNodeId) => v.id.step == w.id.step && v != w
  let badP := (T.map (fun w => (T.filter (fun v => !sib w v && !(tableOf G w).contains v)).length)).sum
  a := { a with apPairsFail := a.apPairsFail + badP }
  if badP != 0 then a := { a with apFail := a.apFail + 1 }
  -- each pick `w` with siblings: S_w = T with only `w` at its step
  for w in T do
    if T.any (fun v => sib w v) then
      let S := T.filter (fun v => !sib w v)
      a := { a with picks := a.picks + 1 }
      if !closedOn G S then a := { a with pickClosedFail := a.pickClosedFail + 1 }
      let Rw := AggressiveReview.reviewAgg { G with gowners := G.gowners.filter (fun q => S.contains q) }
      if isValid Rw then
        a := { a with pickValid := a.pickValid + 1 }
        if S.all (fun q => Rw.gowners.contains q) then a := { a with pickKeeps := a.pickKeeps + 1 }
      if (!closedOn G S || !isValid Rw) && a.firstP == "" then
        a := { a with firstP := s!"{lab}: |T|={T.length}, pick {w.id.step}/{w.id.index}, closed {closedOn G S}, valido {isValid Rw}" }
  if G.nodes.any (fun x => ownsAll G x.owners) then a := { a with anyA := a.anyA + 1 }
  if G.nodes.any (fun x => ownsAll G x.owners && closedOn G x.owners) then
    a := { a with anyWoven := a.anyWoven + 1 }
  if (!aok || !cok) && a.first == "" then
    a := { a with first := s!"{lab}: |T|={T.length}, pares sin poseer {bad}/{pairs}, closed {cok}, algun nodo con (a) {G.nodes.any (fun x => ownsAll G x.owners)}" }
  return a

partial def walkMN (lab : String) (g : GPathM) (fuel : Nat) (a : MNAcc) : MNAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      let mut next : Option GPathM := none
      for q in ownersAt g.gowners k do
        let h := filterAllAgg g [q.id]
        if isValid h then
          a := measureMN lab h a
          if next.isNone then next := some h
      match next with
      | none => return a
      | some h => return walkMN lab h (fuel - 1) a

def runFormulaMN (lab : String) (φ : Cnf) (a : MNAcc) : MNAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := measureMN lab g a
      a := walkMN lab g (stepCount φ).toNat a
  return a

def reportMN (name : String) (a : MNAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   estados del lector: {a.states}; |T| medio {if a.states == 0 then 0 else a.tSize / a.states}"
  IO.println s!"   (sym) algun w de T sin m: {a.symFail}; tablas de m con ids repetidos: {a.dupTables}"
  IO.println s!"   (a) T no contenida en alguna tabla de T: {a.aFail} estados; pares (w,v) con v no en tabla(w): {a.aPairsFail} de {a.aPairs}"
  IO.println s!"   (b) Closed falla: {a.closedFail};  Woven (a y b) se cumple: {a.wovenOk}"
  IO.println s!"   (c) restringir a T y reviewAgg: valido {a.restrictValid}, conserva T entera {a.restrictKeepsT}"
  IO.println s!"   (d) ya resuelto (un owner por paso): {a.solved}; pasos con varios owners (total): {a.multiSteps}"
  IO.println s!"   (any) algun nodo cumple (a): {a.anyA}; alguno cumple Woven: {a.anyWoven}"
  IO.println s!"   (a') T sin los hermanos de w dentro de tabla(w): falla en {a.apFail} estados; pares {a.apPairsFail}"
  IO.println s!"   eleccion w con hermanos: {a.picks}; S_w no Closed {a.pickClosedFail}; restringir a S_w y reviewAgg: valido {a.pickValid}, conserva S_w {a.pickKeeps}"
  if a.firstP != "" then IO.println s!"   primer fallo de eleccion: {a.firstP}"
  if a.first != "" then IO.println s!"   primer fallo: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`minreader`: el lector `ReaderMinOwner` simulado entero.** Desde cada estado inicial del lector
(línea final tras `reviewAgg`): `m` = nodo con menos owners, restringir la global a su tabla y
`reviewAgg`. Después, mientras algún paso tenga más de un owner global: en el primero, probar **cada**
owner `w` (fijar la global de ese paso a `w` y `reviewAgg`) y contar las que dejan el grafo inválido;
seguir con la primera. Al final, con un owner por paso: ¿forman una cadena enlazada por padres? -/

structure MRAcc where
  formulas : Nat := 0
  starts : Nat := 0
  restrictInvalid : Nat := 0
  choicePoints : Nat := 0
  choices : Nat := 0
  choicesInvalid : Nat := 0
  pointsAllInvalid : Nat := 0
  finished : Nat := 0
  chainOk : Nat := 0
  rounds : Nat := 0
  first : String := ""
  deriving Repr

def pinExact (G : GPathM) (w : PathNodeId) : GPathM :=
  { G with gowners := G.gowners.filter (fun q => q.id.step != w.id.step || q == w) }

def ownersAtStep (G : GPathM) (k : Int) : List PathNodeId :=
  (G.gowners.filter (fun q => q.id.step == k)).eraseDups

def chainOf1 (G : GPathM) : Bool :=
  (intRange 0 (G.current_step - 2)).all (fun k =>
    match ownersAtStep G k, ownersAtStep G (k + 1) with
    | [a], [b] => (match G.node? b with | some nb => nb.parents.contains a | none => false)
    | _, _ => false)

partial def minReaderLoop (lab : String) (G : GPathM) (fuel : Nat) (a : MRAcc) : MRAcc :=
  if fuel == 0 then a
  else if !isValid G then a
  else
    match (intRange 0 (G.current_step - 1)).find? (fun k => (ownersAtStep G k).length > 1) with
    | none =>
      let ok := chainOf1 G
      let a := { a with finished := a.finished + 1, chainOk := a.chainOk + (if ok then 1 else 0) }
      if !ok && a.first == "" then { a with first := s!"{lab}: un owner por paso pero sin cadena" } else a
    | some k => Id.run do
      let ws := ownersAtStep G k
      let mut a := { a with choicePoints := a.choicePoints + 1, rounds := a.rounds + 1 }
      let mut next : Option GPathM := none
      let mut bad := 0
      for w in ws do
        let R := AggressiveReview.reviewAgg (pinExact G w)
        a := { a with choices := a.choices + 1 }
        if isValid R then
          if next.isNone then next := some R
        else bad := bad + 1
      a := { a with choicesInvalid := a.choicesInvalid + bad }
      if bad > 0 && a.first == "" then
        a := { a with first := s!"{lab}: paso {k}, {bad} de {ws.length} elecciones dejan el grafo invalido" }
      match next with
      | none => return { a with pointsAllInvalid := a.pointsAllInvalid + 1 }
      | some R => return minReaderLoop lab R (fuel - 1) a

def runFormulaMR (lab : String) (φ : Cnf) (a : MRAcc) : MRAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      match g.nodes.head? with
      | none => pure ()
      | some n0 =>
        let m := g.nodes.foldl (fun b n => if n.owners.length < b.owners.length then n else b) n0
        let T := m.owners
        a := { a with starts := a.starts + 1 }
        let G := AggressiveReview.reviewAgg { g with gowners := g.gowners.filter (fun q => T.contains q) }
        if !isValid G then
          a := { a with restrictInvalid := a.restrictInvalid + 1 }
          if a.first == "" then a := { a with first := s!"{lab}: restringir a T_m deja el grafo invalido" }
        else a := minReaderLoop lab G (stepCount φ).toNat a
  return a

def reportMR (name : String) (a : MRAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   arranques: {a.starts}; restringir a T_m invalido: {a.restrictInvalid}"
  IO.println s!"   puntos de eleccion: {a.choicePoints}; elecciones probadas: {a.choices}; invalidas: {a.choicesInvalid}; puntos sin ninguna valida: {a.pointsAllInvalid}"
  IO.println s!"   terminados con un owner por paso: {a.finished}; de ellos cadena por padres: {a.chainOk}"
  if a.first != "" then IO.println s!"   primer fallo: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`roundseg`: `SegGood` vuelta a vuelta.** En cada vuelta (`reviewPass`, ya con `cleanInvalid₂`) de
la review agresiva de cada envío y de cada pin del lector: con `g` la entrada y `g'` la salida, para
cada tramo `P` de `g'` y cada paso `i` fuera de él, `C(g)` y `C(g')` las entradas comunes a las tablas
de `P`. Como las tablas solo encogen, `C(g') ⊆ C(g)`.

* **S1**: una entrada común de antes que sigue viva en `g'` sigue siendo común;
* **S2**: alguna entrada común de antes sigue viva en `g'`;
* y si `SegGood` vale en `g` y en `g'`. -/

structure RSAcc where
  formulas : Nat := 0
  rounds : Nat := 0
  inputBad : Nat := 0
  cases : Nat := 0
  notSegBefore : Nat := 0
  oldEmpty : Nat := 0
  newEmpty : Nat := 0
  s1Fail : Nat := 0
  s1Clean : Nat := 0
  s2Fail : Nat := 0
  s1m : Nat := 0
  s2m : Nat := 0
  s1lost : Nat := 0
  s1flex : Nat := 0
  firstF : String := ""
  downCases : Nat := 0
  s1c : Nat := 0
  s2c : Nat := 0
  first1 : String := ""
  first2 : String := ""
  deriving Repr

def commonAtRS (g : GPathM) (P : List PathNodeId) (i : Int) : List PathNodeId :=
  let tabs := P.map (fun y => (g.node? y).map (·.owners) |>.getD [])
  ((tabs.headD []).filter (fun r => r.id.step == i && tabs.all (fun t => t.contains r))).eraseDups

def segsOf (g : GPathM) : List (List PathNodeId) := Id.run do
  let mut out : List (List PathNodeId) := []
  for x in g.nodes.take 20 do
    let (segs, _) := collectDown g [x.id] ([], 30)
    out := segs ++ out
  return out

def inputSegGood (g : GPathM) : Bool :=
  (segsOf g).all (fun P =>
    match P.head?, P.getLast? with
    | some lo, some hi =>
      (intRange 0 (g.current_step - 1)).all (fun i =>
        !(i < lo.id.step || hi.id.step < i) || !(commonAtRS g P i).isEmpty)
    | _, _ => true)

def roundRS (lab : String) (g : GPathM) (a : RSAcc) : RSAcc := Id.run do
  let g' := reviewPass g
  if !isValid g' then return a
  let mut a := { a with rounds := a.rounds + 1 }
  if !inputSegGood g then
    a := { a with inputBad := a.inputBad + 1 }
    return a
  let gc := cleanInvalid₂ g
  for P in segsOf g' do
    match P.head?, P.getLast? with
    | some lo, some hi =>
      for i in intRange 0 (g.current_step - 1) do
        if i < lo.id.step || hi.id.step < i then
          a := { a with cases := a.cases + 1 }
          if !isSegment g P then a := { a with notSegBefore := a.notSegBefore + 1 }
          let cOld := commonAtRS g P i
          let cNew := commonAtRS g' P i
          if cOld.isEmpty then a := { a with oldEmpty := a.oldEmpty + 1 }
          if cNew.isEmpty then a := { a with newEmpty := a.newEmpty + 1 }
          let aliveOld := cOld.filter (fun r => (g'.node? r).isSome)
          if aliveOld.isEmpty then
            a := { a with s2Fail := a.s2Fail + 1 }
            if a.first2 == "" then
              a := { a with first2 := s!"{lab}: tramo {lo.id.step}..{hi.id.step}, paso {i}, comunes antes {cOld.length}, vivas 0" }
          -- (A) symmetric entries: r owns every node of P
          let symm := aliveOld.filter (fun r =>
            P.all (fun y => ((g.node? r).map (·.owners) |>.getD []).contains y))
          if symm.any (fun r => !cNew.contains r) then a := { a with s1m := a.s1m + 1 }
          if !symm.any (fun r => cNew.contains r) then a := { a with s2m := a.s2m + 1 }
          -- (B) chained entries below: r is the low end of a descending segment of g through P
          if i < lo.id.step then
            a := { a with downCases := a.downCases + 1 }
            let (ext, _) := collectDown g P ([], 200)
            let chained := aliveOld.filter (fun r => ext.any (fun Q => Q.head? == some r))
            if chained.any (fun r => !cNew.contains r) then a := { a with s1c := a.s1c + 1 }
            if !chained.any (fun r => cNew.contains r) then a := { a with s2c := a.s2c + 1 }
          -- S1': a live common entry that left some table of P — was it still compatible with
          -- every node of P in g' (a common node at every step with each table)?
          let tabNew := fun (y : PathNodeId) => ((g'.node? y).map (·.owners)).getD []
          for r in aliveOld.filter (fun r => !cNew.contains r) do
            -- compatible = a common node at every step other than r's and x's own
            let compat := fun (x : PathNodeId) =>
              (intRange 0 (g'.current_step - 1)).all (fun k =>
                k == r.id.step || k == x.id.step ||
                (tabNew x).any (fun q => q.id.step == k && (tabNew r).contains q))
            let compatAll := P.all compat
            if compatAll then
              a := { a with s1flex := a.s1flex + 1 }
              if a.firstF == "" then
                a := { a with firstF := s!"{lab}: tramo {lo.id.step}..{hi.id.step}, paso {i}, r={r.id.step}/{r.id.index}" }
            else a := { a with s1lost := a.s1lost + 1 }
          if aliveOld.any (fun r => !cNew.contains r) then
            a := { a with s1Fail := a.s1Fail + 1 }
            -- did the clean already drop it from some table of P?
            if aliveOld.any (fun r => !(commonAtRS gc P i).contains r) then
              a := { a with s1Clean := a.s1Clean + 1 }
            if a.first1 == "" then
              a := { a with first1 := s!"{lab}: tramo {lo.id.step}..{hi.id.step}, paso {i}, comunes vivas {aliveOld.length}, siguen comunes {cNew.length}" }
    | _, _ => pure ()
  return a

/-- The aggressive review, instrumented at every base round. -/
def reviewAggRS (lab : String) (F : GPathM) (a : RSAcc) : RSAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure g + 1
  while outer > 0 do
    outer := outer - 1
    -- base review: rounds until the measure stops
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        a := roundRS lab g a
        let g' := reviewPass g
        if GPathM.measure g' < GPathM.measure g then g := g' else
          g := g'
          fuel := 0
    if !isValid g then outer := 0
    else
      let g₂ := AggressiveReview.aggSweep g
      if GPathM.measure g₂ < GPathM.measure g then g := g₂ else outer := 0
  return a

partial def walkRS (lab : String) (g : GPathM) (fuel : Nat) (a : RSAcc) : RSAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := reviewAggRS lab ([q.id].foldl filterRequire g) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkRS lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaRS (lab : String) (φ : Cnf) (sends : Bool) (a : RSAcc) : RSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    if sends then
      for kv in line do
        for d in mapSons φ kv.1.step kv.1.index do
          let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
          a := reviewAggRS lab F a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkRS lab g (stepCount φ).toNat a
  return a

def reportRS (name : String) (a : RSAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   vueltas: {a.rounds}; con SegGood roto a la entrada: {a.inputBad}"
  IO.println s!"   casos (tramo de g', paso fuera): {a.cases}; no era tramo en g: {a.notSegBefore}"
  IO.println s!"   SegGood: sin comun en g {a.oldEmpty}, sin comun en g' {a.newEmpty}"
  IO.println s!"   S1 falla (comun viva que deja de ser comun): {a.s1Fail} (ya en cleanInvalid₂: {a.s1Clean})"
  IO.println s!"   S2 falla (ninguna comun de antes sigue viva): {a.s2Fail}"
  IO.println s!"   S1' entradas vivas que salieron de alguna tabla del tramo: perdieron compatibilidad con algun nodo {a.s1lost}; seguian compatibles con todos {a.s1flex}"
  if a.firstF != "" then IO.println s!"   primer caso compatible que salio: {a.firstF}"
  IO.println s!"   (A) simetricas: S1 falla {a.s1m}; ninguna simetrica sigue comun {a.s2m}"
  IO.println s!"   (B) encadenadas por debajo ({a.downCases} casos): S1 falla {a.s1c}; ninguna encadenada sigue comun {a.s2c}"
  if a.first1 != "" then IO.println s!"   primer S1: {a.first1}"
  if a.first2 != "" then IO.println s!"   primer S2: {a.first2}"
  IO.println s!"   ({ms} ms)"

/-! **`midsym`: la simetría de la posesión a mitad de pasada.** En cada vuelta de la review agresiva
de cada envío y pin del lector, antes de cada `reviewNode` de las dos pasadas:

* estados con algún par vivo asimétrico (`r` tiene a `q`, `q` no tiene a `r`);
* **eventos de corte**: `x` sobrevive y pierde una entrada viva `r`. En cada uno, ¿queda en la nueva
  tabla de `x`, en el paso de los vecinos (x−1 en padres, x+1 en hijos), un nodo `q` que `r` tenga en
  su tabla? Si no, `lost_parents`/`lost_sons` valen ahí (separación en ese paso). Si sí, la simetría
  estaba rota en `(r, q)`: se mira si `x` y `r` siguen sin compartir nada en **algún** otro paso. -/

structure MSAcc where
  formulas : Nat := 0
  states : Nat := 0
  asymStates : Nat := 0
  asymPairs : Nat := 0
  drops : Nat := 0
  sepAtNeighbour : Nat := 0
  asymEvents : Nat := 0
  asymSepElsewhere : Nat := 0
  distHist : List (Int × Nat) := []
  sideBelow : Nat := 0
  sideAbove : Nat := 0
  sepAtQ : Nat := 0
  first : String := ""
  deriving Repr

def ownersOfMS (g : GPathM) (p : PathNodeId) : List PathNodeId :=
  (g.node? p).map (·.owners) |>.getD []

def asymCount (g : GPathM) : Nat :=
  (g.nodes.map (fun nr => (nr.owners.filter (fun q =>
    (g.node? q).isSome && !(ownersOfMS g q).contains nr.id)).length)).sum

def nodeStepMS (lab : String) (g : GPathM) (nb : PNodeM → List PathNodeId) (parents : Bool)
    (x : PathNodeId) (a : MSAcc) : MSAcc × GPathM := Id.run do
  let g' := reviewNode g nb x
  let mut a := { a with states := a.states + 1 }
  let ac := asymCount g
  if ac > 0 then a := { a with asymStates := a.asymStates + 1, asymPairs := a.asymPairs + ac }
  match g.node? x, g'.node? x with
  | some d, some d' =>
    let k := if parents then x.id.step - 1 else x.id.step + 1
    for r in d.owners do
      if (g'.node? r).isSome && !d'.owners.contains r then
        a := { a with drops := a.drops + 1 }
        let tr := ownersOfMS g r
        let bad := d'.owners.filter (fun q => q.id.step == k && tr.contains q)
        if bad.isEmpty then a := { a with sepAtNeighbour := a.sepAtNeighbour + 1 }
        else
          a := { a with asymEvents := a.asymEvents + 1 }
          let tr' := ownersOfMS g' r
          let sepSomewhere := (intRange 0 (g.current_step - 1)).any (fun j =>
            j != r.id.step && j != x.id.step &&
            !(d'.owners.any (fun q => q.id.step == j && tr'.contains q)))
          if sepSomewhere then a := { a with asymSepElsewhere := a.asymSepElsewhere + 1 }
          let seps := (intRange 0 (g.current_step - 1)).filter (fun j =>
            j != r.id.step && j != x.id.step &&
            !(d'.owners.any (fun q => q.id.step == j && tr'.contains q)))
          -- nearest separation step to x, on the side of the pass (below for parents, above for sons)
          let dists := seps.map (fun j => if parents then x.id.step - j else j - x.id.step)
          let pos := dists.filter (fun t => t > 0)
          match pos.min? with
          | some dmin =>
            let key := if dmin ≥ 5 then 5 else dmin
            let h := a.distHist
            let h := match h.find? (fun p => p.1 == key) with
              | some _ => h.map (fun p => if p.1 == key then (p.1, p.2 + 1) else p)
              | none => (key, 1) :: h
            a := { a with distHist := h, sideBelow := a.sideBelow + 1 }
          | none => a := { a with sideAbove := a.sideAbove + 1 }
          -- is it separated at the step where some kept neighbour q (that r owns) lost r?
          let qsteps := bad.map (fun q => if parents then q.id.step - 1 else q.id.step + 1)
          if qsteps.any (fun j => seps.contains j) then a := { a with sepAtQ := a.sepAtQ + 1 }
          if a.first == "" then
            a := { a with first := s!"{lab}: x paso {x.id.step}, r paso {r.id.step}, {if parents then "padres" else "hijos"}, q con r: {bad.length}, separados en otro paso: {sepSomewhere}" }
  | _, _ => pure ()
  return (a, g')

def passMS (lab : String) (g : GPathM) (parents : Bool) (a : MSAcc) : MSAcc × GPathM := Id.run do
  let nb : PNodeM → List PathNodeId := if parents then (·.parents) else (·.sons)
  let ks := if parents then intRange 1 (g.current_step - 1) else (intRange 0 (g.current_step - 2)).reverse
  let mut a := a
  let mut g := g
  for k in ks do
    if !isValid g then break
    for x in (g.line k).map (·.id) do
      let (a', g') := nodeStepMS lab g nb parents x a
      a := a'
      g := g'
  return (a, g)

def reviewAggMS (lab : String) (F : GPathM) (a : MSAcc) : MSAcc := Id.run do
  let mut a := a
  let mut g := F
  let mut outer := GPathM.measure g + 1
  while outer > 0 do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 do
      fuel := fuel - 1
      if !isValid g then fuel := 0
      else
        let g0 := g
        let c := cleanInvalid₂ g
        let (a1, h1) := passMS lab c true a
        let (a2, h2) := passMS lab h1 false a1
        a := a2
        g := h2
        if !(GPathM.measure g < GPathM.measure g0) then fuel := 0
    if !isValid g then outer := 0
    else
      let g₂ := AggressiveReview.aggSweep g
      if GPathM.measure g₂ < GPathM.measure g then g := g₂ else outer := 0
  return a

partial def walkMS (lab : String) (g : GPathM) (fuel : Nat) (a : MSAcc) : MSAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := reviewAggMS lab ([q.id].foldl filterRequire g) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkMS lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaMS (lab : String) (φ : Cnf) (a : MSAcc) : MSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := reviewAggMS lab F a
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkMS lab g (stepCount φ).toNat a
  return a

def reportMS (name : String) (a : MSAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   estados antes de reviewNode: {a.states}; con algun par vivo asimetrico: {a.asymStates} (pares {a.asymPairs})"
  IO.println s!"   eventos de corte (x pierde una r viva): {a.drops}"
  IO.println s!"     separacion en el paso de los vecinos (vale lost_parents/sons): {a.sepAtNeighbour}"
  IO.println s!"     con asimetria (algun q vecino que conserva x lo tiene r): {a.asymEvents}; de ellos separados en otro paso: {a.asymSepElsewhere}"
  IO.println s!"     distancia a la separacion mas cercana del lado de la pasada (5 = 5+): {a.distHist.reverse}; solo del otro lado: {a.sideAbove}"
  IO.println s!"     separados en el paso de los vecinos del q que conserva x (q-1 / q+1): {a.sepAtQ}"
  if a.first != "" then IO.println s!"   primer evento asimetrico: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`segexact`: todo tramo está en una cadena completa.** La versión por tramos de `TablesExact`: en
cada estado válido, cada tramo (enlazado por padres, poseído por pares) ¿se extiende, dentro de la
global, a una cadena completa del paso 0 al último, cuyos miembros se poseen todos entre sí?
Clases: la línea (cada estado tras cada avance y la final revisada), los envíos (tras `reviewAgg`) y
los estados del lector (cada pin, hermanos incluidos). -/

structure SECell where
  states : Nat := 0
  segs : Nat := 0
  notInGow : Nat := 0
  ok : Nat := 0
  bad : Nat := 0
  cut : Nat := 0
  first : String := ""
  deriving Repr

structure SEAcc where
  formulas : Nat := 0
  line : SECell := {}
  sends : SECell := {}
  reader : SECell := {}
  deriving Repr

def checkSE (lab : String) (g : GPathM) (budget : Nat) (c : SECell) : SECell := Id.run do
  if !isValid g then return c
  let mut c := { c with states := c.states + 1 }
  for P in segsOf g do
    c := { c with segs := c.segs + 1 }
    if !P.all (fun p => g.gowners.contains p) then
      c := { c with notInGow := c.notInGow + 1 }
    else
      match (extendFullIn g (fun x => g.gowners.contains x) P budget).1 with
      | some true => c := { c with ok := c.ok + 1 }
      | some false =>
        let msg := s!"{lab}: tramo {(P.head?.map (·.id.step)).getD 0}..{(P.getLast?.map (·.id.step)).getD 0} (long {P.length})"
        c := { c with bad := c.bad + 1, first := if c.first == "" then msg else c.first }
      | none => c := { c with cut := c.cut + 1 }
  return c

partial def walkSE (lab : String) (g : GPathM) (fuel budget : Nat) (c : SECell) : SECell :=
  let c := checkSE lab g budget c
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := checkSE s!"{lab} pin" (filterAllAgg g [q.id]) budget c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkSE lab (filterAllAgg g [q.id]) (fuel - 1) budget c

def runFormulaSE (label : String) (φ : Cnf) (budget : Nat) (a : SEAcc) : SEAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      a := { a with line := checkSE s!"{label} linea paso {step}" kv.2 budget a.line }
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := { a with sends := checkSE s!"{label} envio paso {step}" (AggressiveReview.reviewAgg F) budget a.sends }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    a := { a with line := checkSE s!"{label} linea final" g budget a.line }
    if isValid g then a := { a with reader := walkSE s!"{label} lector" g (stepCount φ).toNat budget a.reader }
  return a

def reportSECell (lbl : String) (c : SECell) : IO Unit := do
  IO.println s!"   {lbl}: estados {c.states}, tramos {c.segs}; en cadena completa {c.ok}, SIN cadena {c.bad}, presupuesto {c.cut}, fuera de la global {c.notInGow}"
  if c.first != "" then IO.println s!"      primer tramo sin cadena: {c.first}"

def reportSE (name : String) (a : SEAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportSECell "linea  " a.line
  reportSECell "envios " a.sends
  reportSECell "lector " a.reader
  IO.println s!"   ({ms} ms)"

/-! **`segmix`: ¿la unión mezcla tramos?** (`SegExactUp.SegNoMix`). En cada `doJoin` real de la
línea: para cada tramo del estado unido, ¿es tramo de `A`, de `B`, o de ninguno (mezclado)? Y los
mezclados, ¿están aun así en una cadena completa del estado unido? -/

structure SMAcc where
  formulas : Nat := 0
  joins : Nat := 0
  segs : Nat := 0
  inA : Nat := 0
  inB : Nat := 0
  mixed : Nat := 0
  mixedInChain : Nat := 0
  mixedNoChain : Nat := 0
  revSegs : Nat := 0
  revMixed : Nat := 0
  revMixedSegGoodFail : Nat := 0
  detail : String := ""
  firstRev : String := ""
  first : String := ""
  deriving Repr

def measureSM (lab : String) (A B : GPathM) (a : SMAcc) : SMAcc := Id.run do
  if !okJoin A B then return a
  let J := join A B
  let mut a := { a with joins := a.joins + 1 }
  for P in segsOf J do
    a := { a with segs := a.segs + 1 }
    if isSegment A P then a := { a with inA := a.inA + 1 }
    else if isSegment B P then a := { a with inB := a.inB + 1 }
    else
      a := { a with mixed := a.mixed + 1 }
      match (extendFullIn J (fun x => J.gowners.contains x) P 5000).1 with
      | some true => a := { a with mixedInChain := a.mixedInChain + 1 }
      | _ => a := { a with mixedNoChain := a.mixedNoChain + 1 }
      if a.first == "" then
        a := { a with first := s!"{lab}: tramo {(P.head?.map (·.id.step)).getD 0}..{(P.getLast?.map (·.id.step)).getD 0}" }
  -- MixDies: the segments of the reviewed join
  let R := AggressiveReview.reviewAgg J
  if isValid R then
    for P in segsOf R do
      a := { a with revSegs := a.revSegs + 1 }
      if !isSegment A P && !isSegment B P then
        a := { a with revMixed := a.revMixed + 1 }
        match P.head?, P.getLast? with
        | some lo, some hi =>
          let badSteps := (intRange 0 (R.current_step - 1)).filter (fun i =>
            (i < lo.id.step || hi.id.step < i) && (commonAtRS R P i).isEmpty)
          if !badSteps.isEmpty then a := { a with revMixedSegGoodFail := a.revMixedSegGoodFail + 1 }
          if a.detail == "" then
            -- which side each node comes from, and which pairs own each other only in the join
            let side := P.map (fun p => (if (A.node? p).isSome then "A" else "") ++ (if (B.node? p).isSome then "B" else ""))
            let onlyJ := (P.filter (fun p => P.any (fun q => p != q && mutuallyOwn R p q && !mutuallyOwn A p q && !mutuallyOwn B p q))).length
            a := { a with detail := s!"cs {R.current_step}, lados {side}, pasos sin comun {badSteps}, nodos con par solo-en-la-union {onlyJ}" }
        | _, _ => pure ()
        if a.firstRev == "" then
          a := { a with firstRev := s!"{lab}: tramo {(P.head?.map (·.id.step)).getD 0}..{(P.getLast?.map (·.id.step)).getD 0}" }
  return a

def runFormulaSM (label : String) (φ : Cnf) (a : SMAcc) : SMAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    let mut next : PureLine := []
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let h := upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
        if isValid h then
          match next.find? (fun e => e.1 == d) with
          | some (_, existing) =>
            a := measureSM s!"{label} paso {step}" existing h a
            next := next.map (fun e => if e.1 == d then (d, doJoin existing h) else e)
          | none => next := next ++ [(d, h)]
    line := next
  return a

def reportSM (name : String) (a : SMAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   uniones {a.joins}, tramos {a.segs}: de A {a.inA}, de B {a.inB}, MEZCLADOS {a.mixed} (en cadena completa {a.mixedInChain}, sin cadena {a.mixedNoChain})"
  IO.println s!"   MixDies: tramos del revisado de la union {a.revSegs}, mezclados (de ningun lado) {a.revMixed}"
  if a.firstRev != "" then IO.println s!"   primer mezclado que sobrevive: {a.firstRev}"
  IO.println s!"   de los mezclados que sobreviven, sin SegGood (algun paso sin comun): {a.revMixedSegGoodFail}"
  if a.detail != "" then IO.println s!"   detalle: {a.detail}"
  if a.first != "" then IO.println s!"   primer mezclado: {a.first}"
  IO.println s!"   ({ms} ms)"

/-! **`segstep`: las dos obligaciones de `SegExactFilter`, en cada filtro de un paso.** En cada envío,
paso a paso (`T` → `R = reviewAgg (filterWeak T e)`), y en cada pin del lector: para cada tramo de `R`
que no cubre el paso filtrado, ¿hay una entrada común admitida en ese paso (`CommonAtFilter`)? y para
cada una, ¿están tramo y entrada en una cadena completa de `T` (`StepSegTriples`)? -/

structure SSCell where
  filters : Nat := 0
  segs : Nat := 0
  covering : Nat := 0
  noCommon : Nat := 0
  triples : Nat := 0
  triplesBad : Nat := 0
  cut : Nat := 0
  firstC : String := ""
  firstT : String := ""
  deriving Repr

structure SSAcc where
  formulas : Nat := 0
  sends : SSCell := {}
  pins : SSCell := {}
  deriving Repr

def checkSS (lab : String) (T : GPathM) (e : Int × List NodeId) (c : SSCell) : SSCell := Id.run do
  let R := AggressiveReview.reviewAgg (PureDriverImproves.filterWeak T e)
  if !isValid R then return c
  let mut c := { c with filters := c.filters + 1 }
  for P in segsOf R do
    match P.head?, P.getLast? with
    | some lo, some hi =>
      c := { c with segs := c.segs + 1 }
      if lo.id.step ≤ e.1 && e.1 ≤ hi.id.step then c := { c with covering := c.covering + 1 }
      else
        let cs := (commonAtRS R P e.1).filter (fun q => R.gowners.contains q)
        if cs.isEmpty then
          c := { c with noCommon := c.noCommon + 1 }
          if c.firstC == "" then c := { c with firstC := s!"{lab}: tramo {lo.id.step}..{hi.id.step}, paso {e.1}" }
        for q in cs do
          c := { c with triples := c.triples + 1 }
          let ok := fun x => T.gowners.contains x && (x.id.step != e.1 || x == q)
          match (extendFullIn T ok P 5000).1 with
          | some true => pure ()
          | some false =>
            c := { c with triplesBad := c.triplesBad + 1 }
            if c.firstT == "" then c := { c with firstT := s!"{lab}: tramo {lo.id.step}..{hi.id.step}, c paso {e.1}" }
          | none => c := { c with cut := c.cut + 1 }
    | _, _ => pure ()
  return c

partial def walkSS (lab : String) (g : GPathM) (fuel : Nat) (c : SSCell) : SSCell :=
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := checkSS s!"{lab} pin" g (k, [q.id]) c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkSS lab (filterAllAgg g [q.id]) (fuel - 1) c

def runFormulaSS (label : String) (φ : Cnf) (a : SSAcc) : SSAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        for e in es do
          if isValid T then
            a := { a with sends := checkSS s!"{label} envio paso {step}" T e a.sends }
            T := AggressiveReview.reviewAgg (PureDriverImproves.filterWeak T e)
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := { a with pins := walkSS s!"{label} lector" g (stepCount φ).toNat a.pins }
  return a

def reportSSCell (lbl : String) (c : SSCell) : IO Unit := do
  IO.println s!"   {lbl}: filtros {c.filters}, tramos {c.segs} (cubren el paso {c.covering})"
  IO.println s!"      CommonAtFilter: tramos sin comun admitida {c.noCommon}"
  IO.println s!"      StepSegTriples: (tramo, c) {c.triples}, sin cadena en T {c.triplesBad}, presupuesto {c.cut}"
  if c.firstC != "" then IO.println s!"      primer sin comun: {c.firstC}"
  if c.firstT != "" then IO.println s!"      primer sin cadena: {c.firstT}"

def reportSS (name : String) (a : SSAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportSSCell "envios" a.sends
  reportSSCell "pines " a.pins
  IO.println s!"   ({ms} ms)"

/-! **`baddie`: ¿dónde mueren los tramos sin cadena?** En cada estado de la línea, revisado
(`T0 = reviewAgg kv.2`): los tramos sin cadena completa. Para cada envío del paso siguiente, se siguen
filtro a filtro (`T ← reviewAgg (filterWeak T e)`) y tras el `up` final del envío: ¿en qué filtro dejan
de ser tramo? ¿sobreviven al envío entero? ¿y en el lector (la línea final revisada y sus pines)? -/

structure BDAcc where
  formulas : Nat := 0
  lineStates : Nat := 0
  badStates : Nat := 0
  bads : Nat := 0
  badMixedLike : Nat := 0
  tracks : Nat := 0
  dieAt : List (Nat × Nat) := []
  sendInvalid : Nat := 0
  surviveSend : Nat := 0
  surviveStillBad : Nat := 0
  readerBad : Nat := 0
  -- each filter alone, from T0: (class, kills, total); class 0 = in the gap, 1 = inside, 2 = elsewhere
  cls : List (Nat × Nat × Nat) := [(0, 0, 0), (1, 0, 0), (2, 0, 0)]
  firstCls : List (Nat × Nat) := []
  cutsNothing : Nat := 0
  gapInfo : String := ""
  fixInfo : String := ""
  first : String := ""
  firstSurv : String := ""
  deriving Repr

def bumpDie (h : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) :=
  match h.find? (fun p => p.1 == k) with
  | some _ => h.map (fun p => if p.1 == k then (p.1, p.2 + 1) else p)
  | none => (k, 1) :: h

def noChain (g : GPathM) (P : List PathNodeId) : Bool :=
  match (extendFullIn g (fun x => g.gowners.contains x) P 5000).1 with
  | some false => true
  | _ => false

def runFormulaBD (label : String) (φ : Cnf) (a : BDAcc) : BDAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      let T0 := AggressiveReview.reviewAgg kv.2
      if !isValid T0 then continue
      a := { a with lineStates := a.lineStates + 1 }
      let bads := (segsOf T0).filter (fun P => noChain T0 P)
      if bads.isEmpty then continue
      a := { a with badStates := a.badStates + 1, bads := a.bads + bads.length }
      -- is T0 really a fixpoint of every stage?
      let rp := reviewPass T0
      let sw := AggressiveReview.aggSweep T0
      let c2 := cleanInvalid₂ T0
      let pp := reviewParents T0
      let ps := reviewSons T0
      let fix := s!"medida T0 {GPathM.measure T0}; tras cleanInvalid₂ {GPathM.measure c2}, padres {GPathM.measure pp}, hijos {GPathM.measure ps}, reviewPass {GPathM.measure rp}, aggSweep {GPathM.measure sw}; tramos malos tras cada uno: clean {((bads.filter (fun P => isSegment c2 P)).length)}, pass {((bads.filter (fun P => isSegment rp P)).length)}, sweep {((bads.filter (fun P => isSegment sw P)).length)}"
      a := { a with fixInfo := a.fixInfo ++ s!" | {fix}" }
      if a.first == "" then a := { a with first := s!"{label} paso {step}: {bads.length} tramos sin cadena" }
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        -- every filter alone, classified against each bad segment's gap
        for P in bads do
          match P.head?, P.getLast? with
          | some lo, some hi =>
            let gap := (intRange 0 (T0.current_step - 1)).filter (fun i =>
              (i < lo.id.step || hi.id.step < i) && (commonAtRS T0 P i).isEmpty)
            if a.gapInfo == "" then
              a := { a with gapInfo := s!"tramo {lo.id.step}..{hi.id.step}, cs {T0.current_step}, hueco {gap}, filtros del envio en pasos {es.map (·.1)}" }
            let classOf := fun (k : Int) => if gap.contains k then 0 else if lo.id.step ≤ k && k ≤ hi.id.step then 1 else 2
            let mut firstDone := false
            for e in es do
              let F := PureDriverImproves.filterWeak T0 e
              if F.gowners.length == T0.gowners.length then a := { a with cutsNothing := a.cutsNothing + 1 }
              let R := AggressiveReview.reviewAgg F
              let kills := !isValid R || !isSegment R P
              let c := classOf e.1
              a := { a with cls := a.cls.map (fun t => if t.1 == c then (t.1, t.2.1 + (if kills then 1 else 0), t.2.2 + 1) else t) }
              if !firstDone then
                firstDone := true
                a := { a with firstCls := bumpDie a.firstCls c }
          | _, _ => pure ()
        for P in bads do
          a := { a with tracks := a.tracks + 1 }
          let mut T := T0
          let mut dead := false
          let mut idx := 0
          for e in es do
            if !dead then
              idx := idx + 1
              T := AggressiveReview.reviewAgg (PureDriverImproves.filterWeak T e)
              if !isValid T then
                a := { a with sendInvalid := a.sendInvalid + 1 }
                dead := true
              else if !isSegment T P then
                a := { a with dieAt := bumpDie a.dieAt idx }
                dead := true
          if !dead then
            let h := upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
            if isValid h && isSegment h P then
              a := { a with surviveSend := a.surviveSend + 1 }
              if noChain h P then a := { a with surviveStillBad := a.surviveStillBad + 1 }
              if a.firstSurv == "" then
                a := { a with firstSurv := s!"{label} paso {step} → ⟨{d.step},{d.index}⟩, {es.length} filtros" }
            else a := { a with dieAt := bumpDie a.dieAt 99 }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with readerBad := a.readerBad + ((segsOf g).filter (fun P => noChain g P)).length }
  return a

def reportBD (name : String) (a : BDAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   estados de la linea revisados {a.lineStates}; con tramos sin cadena {a.badStates} ({a.bads} tramos)"
  IO.println s!"   seguimientos (tramo × envio) {a.tracks}: muere en el filtro n (99 = en el up) {a.dieAt.reverse}; envio invalido {a.sendInvalid}"
  IO.println s!"   SOBREVIVE al envio entero {a.surviveSend} (y sigue sin cadena {a.surviveStillBad})"
  IO.println s!"   lector (linea final revisada): tramos sin cadena {a.readerBad}"
  IO.println s!"   cada filtro solo, desde T0 — (clase, lo mata, total), clase 0 = en el hueco, 1 = dentro del tramo, 2 = fuera con comun: {a.cls}"
  IO.println s!"   clase del PRIMER filtro: {a.firstCls.reverse}; filtros que no quitan nada de la global: {a.cutsNothing}"
  if a.gapInfo != "" then IO.println s!"   ejemplo: {a.gapInfo}"
  IO.println s!"   punto fijo de T0:{a.fixInfo}"
  if a.first != "" then IO.println s!"   primero: {a.first}"
  if a.firstSurv != "" then IO.println s!"   primer superviviente: {a.firstSurv}"
  IO.println s!"   ({ms} ms)"

/-! **`mixtrace`: por qué un corte lejano mata un tramo mezclado.** Para cada tramo sin cadena de una
unión revisada `T0` y cada filtro que corta, se rehace el review agresivo a mano, etapa a etapa
(`cleanInvalid₂`, padres, hijos, barrido agresivo) y se anota la primera etapa en que el tramo deja de
serlo, y por qué: un nodo eliminado, un enlace perdido, o una posesión mutua perdida. -/

structure MTAcc where
  formulas : Nat := 0
  cases : Nat := 0
  stage : List (String × Nat) := []
  reason : List (String × Nat) := []
  firstStory : String := ""
  deriving Repr

def bumpS (h : List (String × Nat)) (k : String) : List (String × Nat) :=
  match h.find? (fun p => p.1 == k) with
  | some _ => h.map (fun p => if p.1 == k then (p.1, p.2 + 1) else p)
  | none => (k, 1) :: h

/-- Why `P` stopped being a segment in `h` (it was one in `g`). -/
def whyBroken (g h : GPathM) (P : List PathNodeId) : String :=
  if P.any (fun p => (h.node? p).isNone) then
    let dead := P.filter (fun p => (h.node? p).isNone)
    s!"nodo eliminado (pasos {dead.map (·.id.step)})"
  else if !(List.range (P.length - 1)).all (fun k =>
      match P[k + 1]?, P[k]? with
      | some hi, some lo => (match h.node? hi with | some n => n.parents.contains lo | none => false)
      | _, _ => false) then "enlace de padre perdido"
  else
    let pairs := P.flatMap (fun p => P.filterMap (fun q =>
      if p != q && mutuallyOwn g p q && !mutuallyOwn h p q then some (p.id.step, q.id.step) else none))
    s!"posesion mutua perdida {pairs.take 3}"

def traceMT (lab : String) (T0 : GPathM) (P : List PathNodeId) (e : Int × List NodeId) (a : MTAcc) :
    MTAcc := Id.run do
  let F := PureDriverImproves.filterWeak T0 e
  if F.gowners.length == T0.gowners.length then return a
  let mut a := { a with cases := a.cases + 1 }
  let mut g := F
  let mut story : List String := []
  let mut done := false
  let mut outer := GPathM.measure g + 1
  while outer > 0 && !done do
    outer := outer - 1
    let mut fuel := GPathM.measure g + 1
    while fuel > 0 && !done do
      fuel := fuel - 1
      if !isValid g then
        a := { a with stage := bumpS a.stage "invalido", reason := bumpS a.reason "grafo invalido" }
        done := true
      else
        let g0 := g
        let stages : List (String × (GPathM → GPathM)) :=
          [("cleanInvalid₂", cleanInvalid₂), ("padres", reviewParents), ("hijos", reviewSons)]
        for (nm, f) in stages do
          if !done then
            let h := f g
            story := story ++ [s!"{nm}: medida {GPathM.measure g}→{GPathM.measure h}"]
            if !isSegment h P then
              let why := whyBroken g h P
              a := { a with stage := bumpS a.stage nm, reason := bumpS a.reason why }
              if a.firstStory == "" then
                a := { a with firstStory := s!"{lab} filtro paso {e.1}: {story} → roto en {nm}: {why}" }
              done := true
            g := h
        if !done && !(GPathM.measure g < GPathM.measure g0) then fuel := 0
    if !done then
      if !isValid g then outer := 0
      else
        let h := AggressiveReview.aggSweep g
        if !isSegment h P then
          let why := whyBroken g h P
          a := { a with stage := bumpS a.stage "aggSweep", reason := bumpS a.reason why }
          if a.firstStory == "" then
            a := { a with firstStory := s!"{lab} filtro paso {e.1}: {story} → roto en aggSweep: {why}" }
          done := true
        else if GPathM.measure h < GPathM.measure g then g := h else outer := 0
  if !done then a := { a with stage := bumpS a.stage "sobrevive" }
  return a

def runFormulaMT (label : String) (φ : Cnf) (a : MTAcc) : MTAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      let T0 := AggressiveReview.reviewAgg kv.2
      if !isValid T0 then continue
      let bads := (segsOf T0).filter (fun P => noChain T0 P)
      if bads.isEmpty then continue
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        for P in bads.take 3 do
          for e in es do
            a := traceMT s!"{label} paso {step}" T0 P e a
    line := pureAdvanceW φ line
  return a

def reportMT (name : String) (a : MTAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   casos (tramo sin cadena × filtro que corta): {a.cases}"
  IO.println s!"   etapa en que se rompe: {a.stage.reverse}"
  IO.println s!"   por que: {a.reason.reverse}"
  if a.firstStory != "" then IO.println s!"   ejemplo: {a.firstStory}"
  IO.println s!"   ({ms} ms)"

/-! **`admtrace`: cómo mata el review un tramo sin salida admitida.** Antes de cada filtro de un paso
(los de los envíos, paso a paso, y los pines del lector): los tramos que no cubren el paso filtrado y
no tienen ninguna cadena completa por un nodo admitido allí («condenados» por `AdmittedExt`). Se sigue
cada uno por el review, etapa a etapa (`traceMT`), y se cuenta si alguno sobrevive. -/

structure ATAcc where
  formulas : Nat := 0
  filters : Nat := 0
  doomed : Nat := 0
  distHist : List (Int × Nat) := []
  someNodeNoAdm : Nat := 0
  nearestNoAdm : Nat := 0
  allHaveAdm : Nat := 0
  firstAll : String := ""
  mt : MTAcc := {}
  deriving Repr

def doomedSegs (T : GPathM) (e : Int × List NodeId) : List (List PathNodeId) :=
  (segsOf T).filter (fun P =>
    match P.head?, P.getLast? with
    | some lo, some hi =>
      (e.1 < lo.id.step || hi.id.step < e.1) &&
      (match (extendFullIn T (fun x => T.gowners.contains x &&
          (x.id.step != e.1 || e.2.contains x.id)) P 5000).1 with
       | some false => true
       | _ => false)
    | _, _ => false)

def atFilter (lab : String) (T : GPathM) (e : Int × List NodeId) (a : ATAcc) : ATAcc := Id.run do
  let mut a := { a with filters := a.filters + 1 }
  for P in (doomedSegs T e).take 6 do
    a := { a with doomed := a.doomed + 1 }
    match P.head?, P.getLast? with
    | some lo, some hi =>
      let dist := if e.1 < lo.id.step then lo.id.step - e.1 else e.1 - hi.id.step
      let key := if dist ≥ 5 then 5 else dist
      a := { a with distHist := match a.distHist.find? (fun p => p.1 == key) with
        | some _ => a.distHist.map (fun p => if p.1 == key then (p.1, p.2 + 1) else p)
        | none => (key, 1) :: a.distHist }
    | _, _ => pure ()
    -- does some node of P (or the nearest one) have no admitted entry at the filtered step?
    let admAt := fun (p : PathNodeId) => ((T.node? p).map (·.owners) |>.getD []).any (fun r =>
      r.id.step == e.1 && e.2.contains r.id && T.gowners.contains r)
    let nearest := match P.head?, P.getLast? with
      | some lo, some hi => if e.1 < lo.id.step then lo else hi
      | _, _ => P.headD default
    if P.any (fun p => !admAt p) then a := { a with someNodeNoAdm := a.someNodeNoAdm + 1 }
    else
      a := { a with allHaveAdm := a.allHaveAdm + 1 }
      if a.firstAll == "" then a := { a with firstAll := s!"{lab} filtro paso {e.1}, tramo {(P.head?.map (·.id.step)).getD 0}..{(P.getLast?.map (·.id.step)).getD 0}" }
    if !admAt nearest then a := { a with nearestNoAdm := a.nearestNoAdm + 1 }
    a := { a with mt := traceMT lab T P e a.mt }
  return a

partial def walkAT (lab : String) (g : GPathM) (fuel : Nat) (a : ATAcc) : ATAcc :=
  if fuel == 0 then a
  else
    match ReaderExec.firstChoice g with
    | none => a
    | some k => Id.run do
      let mut a := a
      for q in ownersAt g.gowners k do
        a := atFilter s!"{lab} pin" g (k, [q.id]) a
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return a
      | some q => return walkAT lab (filterAllAgg g [q.id]) (fuel - 1) a

def runFormulaAT (label : String) (φ : Cnf) (a : ATAcc) : ATAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        for e in es do
          if isValid T then
            a := atFilter s!"{label} envio paso {step}" T e a
            T := AggressiveReview.reviewAgg (PureDriverImproves.filterWeak T e)
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := walkAT s!"{label} lector" g (stepCount φ).toNat a
  return a

def reportAT (name : String) (a : ATAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  IO.println s!"   filtros {a.filters}; tramos condenados seguidos {a.doomed}; distancia al paso filtrado (5 = 5+): {a.distHist.reverse}"
  IO.println s!"   condenados con algun nodo SIN entrada admitida en el paso filtrado: {a.someNodeNoAdm} (el mas cercano sin ella: {a.nearestNoAdm}); con TODOS teniendola: {a.allHaveAdm}"
  if a.firstAll != "" then IO.println s!"      primero con todos teniendola: {a.firstAll}"
  IO.println s!"   (filtros que no cortan no se siguen) casos seguidos {a.mt.cases}"
  IO.println s!"   etapa en que se rompe: {a.mt.stage.reverse}"
  IO.println s!"   por que: {(a.mt.reason.reverse).take 12}"
  if a.mt.firstStory != "" then IO.println s!"   ejemplo: {a.mt.firstStory}"
  IO.println s!"   ({ms} ms)"

/-! **`nodeadm`: `NodeAdmToChain` partido en dos.** Antes de cada filtro de un paso (envíos paso a paso
y pines del lector), para cada tramo `P` que no cubre el paso filtrado y cuyos nodos tienen TODOS una
entrada admitida (de la global) en ese paso:

* la conclusión: ¿cadena completa por `P` y un nodo admitido? (`NodeAdmToChain`);
* (a) Helly en un paso: ¿hay UNA entrada admitida común a todas las tablas de `P`?
* (b) de la común a la cadena: para cada entrada común `r` (admitida o no), ¿cadena completa por `P` y
  `r`? -/

structure NACell where
  cases : Nat := 0
  chain : Nat := 0
  noChain : Nat := 0
  commonAdm : Nat := 0
  noCommonAdm : Nat := 0
  noCommonButChain : Nat := 0
  bCommon : Nat := 0
  bChain : Nat := 0
  bNoChain : Nat := 0
  cut : Nat := 0
  firstA : String := ""
  firstB : String := ""
  deriving Repr

structure NAAcc where
  formulas : Nat := 0
  sends : NACell := {}
  pins : NACell := {}
  deriving Repr

def naFilter (lab : String) (T : GPathM) (e : Int × List NodeId) (c : NACell) : NACell := Id.run do
  let mut c := c
  let admIn := fun (x : PathNodeId) => T.gowners.contains x && x.id.step == e.1 && e.2.contains x.id
  let tab := fun (p : PathNodeId) => ((T.node? p).map (·.owners)).getD []
  for P in segsOf T do
    match P.head?, P.getLast? with
    | some lo, some hi =>
      if (e.1 < lo.id.step || hi.id.step < e.1) && P.all (fun p => (tab p).any admIn) then
        c := { c with cases := c.cases + 1 }
        let okAdm := fun x => T.gowners.contains x && (x.id.step != e.1 || e.2.contains x.id)
        let hasChain := match (extendFullIn T okAdm P 5000).1 with
          | some true => some true | some false => some false | none => none
        match hasChain with
        | some true => c := { c with chain := c.chain + 1 }
        | some false => c := { c with noChain := c.noChain + 1 }
        | none => c := { c with cut := c.cut + 1 }
        let commons := (tab (P.headD lo)).filter (fun r => r.id.step == e.1 && P.all (fun p => (tab p).contains r)) |>.eraseDups
        if commons.any admIn then c := { c with commonAdm := c.commonAdm + 1 }
        else
          c := { c with noCommonAdm := c.noCommonAdm + 1 }
          if hasChain == some true then c := { c with noCommonButChain := c.noCommonButChain + 1 }
          if c.firstA == "" then c := { c with firstA := s!"{lab} filtro paso {e.1}, tramo {lo.id.step}..{hi.id.step}, comunes {commons.length}, cadena {hasChain}" }
        for r in commons do
          c := { c with bCommon := c.bCommon + 1 }
          let okR := fun x => T.gowners.contains x && (x.id.step != e.1 || x == r)
          match (extendFullIn T okR P 5000).1 with
          | some true => c := { c with bChain := c.bChain + 1 }
          | some false =>
            c := { c with bNoChain := c.bNoChain + 1 }
            if c.firstB == "" then c := { c with firstB := s!"{lab} filtro paso {e.1}, tramo {lo.id.step}..{hi.id.step}, r admitida {admIn r}" }
          | none => c := { c with cut := c.cut + 1 }
    | _, _ => pure ()
  return c

partial def walkNA (lab : String) (g : GPathM) (fuel : Nat) (c : NACell) : NACell :=
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := naFilter s!"{lab} pin" g (k, [q.id]) c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkNA lab (filterAllAgg g [q.id]) (fuel - 1) c

def runFormulaNA (label : String) (φ : Cnf) (a : NAAcc) : NAAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let es := weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))
        let mut T := AggressiveReview.reviewAgg kv.2
        for e in es do
          if isValid T then
            a := { a with sends := naFilter s!"{label} envio paso {step}" T e a.sends }
            T := AggressiveReview.reviewAgg (PureDriverImproves.filterWeak T e)
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then a := { a with pins := walkNA s!"{label} lector" g (stepCount φ).toNat a.pins }
  return a

def reportNACell (lbl : String) (c : NACell) : IO Unit := do
  IO.println s!"   {lbl}: tramos con TODOS los nodos con entrada admitida {c.cases}; con cadena admitida {c.chain}, SIN {c.noChain}, presupuesto {c.cut}"
  IO.println s!"      (a) hay entrada admitida COMUN: {c.commonAdm}; no la hay: {c.noCommonAdm} (de esos, con cadena igualmente: {c.noCommonButChain})"
  IO.println s!"      (b) entradas comunes r (cualquiera): {c.bCommon}; con cadena por P y r {c.bChain}, SIN {c.bNoChain}"
  if c.firstA != "" then IO.println s!"      primero sin comun admitida: {c.firstA}"
  if c.firstB != "" then IO.println s!"      primera comun sin cadena: {c.firstB}"

def reportNA (name : String) (a : NAAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportNACell "envios" a.sends
  reportNACell "pines " a.pins
  IO.println s!"   ({ms} ms)"

/-! **`nested`: la tabla del nodo más cercano es la más pequeña.** En cada estado del lector (inicio y
pines, hermanos incluidos) y en los envíos revisados: para cada tramo y cada paso `k` fuera de él, ¿las
entradas en `k` de la tabla del nodo del tramo más cercano a `k` están en las tablas de todos los demás
nodos del tramo? Si sí, `CommonAdm` es inmediata. -/

structure NECell where
  states : Nat := 0
  cases : Nat := 0
  nestedOk : Nat := 0
  nestedFail : Nat := 0
  failEntries : Nat := 0
  totalEntries : Nat := 0
  first : String := ""
  deriving Repr

structure NEAcc where
  formulas : Nat := 0
  sends : NECell := {}
  reader : NECell := {}
  start : NECell := {}
  deriving Repr

def checkNE (lab : String) (g : GPathM) (c : NECell) : NECell := Id.run do
  if !isValid g then return c
  let mut c := { c with states := c.states + 1 }
  let tab := fun (p : PathNodeId) => ((g.node? p).map (·.owners)).getD []
  for P in segsOf g do
    match P.head?, P.getLast? with
    | some lo, some hi =>
      for k in intRange 0 (g.current_step - 1) do
        if k < lo.id.step || hi.id.step < k then
          let near := if k < lo.id.step then lo else hi
          let entries := ((tab near).filter (fun r => r.id.step == k && g.gowners.contains r)).eraseDups
          let bad := entries.filter (fun r => !P.all (fun p => (tab p).contains r))
          c := { c with cases := c.cases + 1, totalEntries := c.totalEntries + entries.length,
                        failEntries := c.failEntries + bad.length }
          if bad.isEmpty then c := { c with nestedOk := c.nestedOk + 1 }
          else
            c := { c with nestedFail := c.nestedFail + 1 }
            if c.first == "" then
              c := { c with first := s!"{lab}: tramo {lo.id.step}..{hi.id.step}, paso {k}, entradas del cercano {entries.length}, no comunes {bad.length}" }
    | _, _ => pure ()
  return c

partial def walkNE (lab : String) (g : GPathM) (fuel : Nat) (c : NECell) : NECell :=
  let c := checkNE lab g c
  if fuel == 0 then c
  else
    match ReaderExec.firstChoice g with
    | none => c
    | some k => Id.run do
      let mut c := c
      for q in ownersAt g.gowners k do
        c := checkNE s!"{lab} pin" (filterAllAgg g [q.id]) c
      match (ownersAt g.gowners k).find? (fun q => isValid (filterAllAgg g [q.id])) with
      | none => return c
      | some q => return walkNE lab (filterAllAgg g [q.id]) (fuel - 1) c

def runFormulaNE (label : String) (φ : Cnf) (a : NEAcc) : NEAcc := Id.run do
  let mut a := { a with formulas := a.formulas + 1 }
  let mut line : PureLine := pureInit φ
  for step in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        let F := (reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d))
        a := { a with sends := checkNE s!"{label} envio paso {step}" (AggressiveReview.reviewAgg F) a.sends }
    line := pureAdvanceW φ line
  for kv in line do
    let g := filterAllAgg kv.2 []
    if isValid g then
      a := { a with start := checkNE s!"{label} inicio" g a.start }
      a := { a with reader := walkNE s!"{label} lector" g (stepCount φ).toNat a.reader }
  return a

def reportNECell (lbl : String) (c : NECell) : IO Unit := do
  IO.println s!"   {lbl}: estados {c.states}, (tramo, paso fuera) {c.cases}: anidado {c.nestedOk}, NO {c.nestedFail} (entradas del cercano no comunes {c.failEntries} de {c.totalEntries})"
  if c.first != "" then IO.println s!"      primero: {c.first}"

def reportNE (name : String) (a : NEAcc) (ms : Nat) : IO Unit := do
  IO.println s!"── {name}  ({a.formulas} formulas)"
  reportNECell "envios" a.sends
  reportNECell "lector" a.reader
  reportNECell "  de ellos, el primer estado" a.start
  IO.println s!"   ({ms} ms)"

def loadCnf (path : String) : IO (Option Cnf) := do
  let txt ← IO.FS.readFile path
  match AbsSat.Cnf.Dimacs.parse (txt.splitOn "\n") with
  | .error _ => return none
  | .ok φ => return (if AbsSat.Cnf.Dimacs.wfB φ then some φ else none)

def randomCnfs (cases nvMin seed : Nat) : List Cnf := Id.run do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed seed
  let mut out : List Cnf := []
  for idx in [0:cases] do
    let (rng1, nv) := rng.below 3
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
    | .ok φ => if AbsSat.Cnf.Dimacs.wfB φ then out := out ++ [φ]
  return out

end Probes.RowDegree

open Probes.RowDegree in
def main (args : List String) : IO Unit := do
  match args with
  | "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormula φ {})
        let t1 ← IO.monoMsNow
        report path a (t1 - t0)
  | "soundat" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaA φ {})
        let t1 ← IO.monoMsNow
        reportA path a (t1 - t0)
  | "soundat" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : AAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaA φ a
      let t1 ← IO.monoMsNow
      reportA s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "filt" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaF2 φ {})
        let t1 ← IO.monoMsNow
        reportF2 path a (t1 - t0)
  | "filt" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : FAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaF2 φ a
      let t1 ← IO.monoMsNow
      reportF2 s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pinchoice" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaPC φ {})
        let t1 ← IO.monoMsNow
        reportPC path a (t1 - t0)
  | "pinchoice" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : PCAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaPC φ a
      let t1 ← IO.monoMsNow
      reportPC s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "owntable" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaOT φ 40 {})
        let t1 ← IO.monoMsNow
        reportOT path a (t1 - t0)
  | "owntable" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : OTAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaOT φ 40 a
      let t1 ← IO.monoMsNow
      reportOT s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "hopdown" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaHD φ 40 {})
        let t1 ← IO.monoMsNow
        reportHD path a (t1 - t0)
  | "hopdown" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : HDAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaHD φ 40 a
      let t1 ← IO.monoMsNow
      reportHD s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "hopdown2" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaHD2 φ 40 {})
        let t1 ← IO.monoMsNow
        reportHD2 path a (t1 - t0)
  | "hopdown2" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : HD2Acc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaHD2 φ 40 a
      let t1 ← IO.monoMsNow
      reportHD2 s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "clique" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaCQ φ 40 {})
        let t1 ← IO.monoMsNow
        reportCQ path a (t1 - t0)
  | "clique" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : CQAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaCQ φ 40 a
      let t1 ← IO.monoMsNow
      reportCQ s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "tablechain" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTC φ 40 {})
        let t1 ← IO.monoMsNow
        reportTC path a (t1 - t0)
  | "tablechain" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TCAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTC φ 40 a
      let t1 ← IO.monoMsNow
      reportTC s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "filterkillcs" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaFKC path φ 20 2000 {})
        let t1 ← IO.monoMsNow
        reportFKC path a (t1 - t0)
  | "filterkillcs" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : FKCAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaFKC s!"seed {seed} #{idx}" φ 20 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportFKC s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "joinext" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaJX path φ 20 2000 {})
        let t1 ← IO.monoMsNow
        reportJX path a (t1 - t0)
  | "joinext" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : JXAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaJX s!"seed {seed} #{idx}" φ 20 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportJX s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "ext1" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaE1 path φ 2000 {})
        let t1 ← IO.monoMsNow
        reportE1 path a (t1 - t0)
  | "ext1" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : E1Acc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaE1 s!"seed {seed} #{idx}" φ 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportE1 s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pairext" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let c ← IO.lazyPure (fun _ => runFormulaPX path φ 2000 {})
        let t1 ← IO.monoMsNow
        reportPX path c (t1 - t0)
  | "pairext" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut c : PXCell := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        c := runFormulaPX s!"seed {seed} #{idx}" φ 2000 c
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportPX s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" c (t1 - t0)
  | "seqsend" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSQ path φ 2000 {})
        let t1 ← IO.monoMsNow
        reportSQ path a (t1 - t0)
  | "seqsend" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SQAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSQ s!"seed {seed} #{idx}" φ 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSQ s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pairall" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let c ← IO.lazyPure (fun _ => runFormulaPA path φ 2000 {})
        let t1 ← IO.monoMsNow
        reportPX path c (t1 - t0)
  | "pairall" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut c : PXCell := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        c := runFormulaPA s!"seed {seed} #{idx}" φ 2000 c
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportPX s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" c (t1 - t0)
  | "pairline" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaPL path φ 2000 {})
        let t1 ← IO.monoMsNow
        reportPL path a (t1 - t0)
  | "pairline" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : PLAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaPL s!"seed {seed} #{idx}" φ 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportPL s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "triplestep" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaT3 path φ 2000 {})
        let t1 ← IO.monoMsNow
        reportT3 path a (t1 - t0)
  | "triplestep" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : T3Acc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaT3 s!"seed {seed} #{idx}" φ 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportT3 s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "nest" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaNS path φ {})
        let t1 ← IO.monoMsNow
        reportNS path a (t1 - t0)
  | "nest" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : NSAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaNS s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportNS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "topkill" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTK path φ {})
        let t1 ← IO.monoMsNow
        reportTK path a (t1 - t0)
  | "topkill" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TKAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTK s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportTK s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "toptrace" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTT path φ {})
        let t1 ← IO.monoMsNow
        reportTT path a (t1 - t0)
  | "toptrace" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TTAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTT s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportTT s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "topmin" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTM path φ {})
        let t1 ← IO.monoMsNow
        reportTM path a (t1 - t0)
  | "topmin" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TMAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTM s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportTM s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "sandwich" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSW path φ {})
        let t1 ← IO.monoMsNow
        reportSW path a (t1 - t0)
  | "sandwich" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SWAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSW s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSW s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "fusion" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaFU φ {})
        let t1 ← IO.monoMsNow
        reportFU path a (t1 - t0)
  | "fusion" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : FUAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaFU φ a
      let t1 ← IO.monoMsNow
      reportFU s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "fusrow" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaFR φ {})
        let t1 ← IO.monoMsNow
        reportFR path a (t1 - t0)
  | "fusrow" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : FRAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaFR φ a
      let t1 ← IO.monoMsNow
      reportFR s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "anchordist" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaAD φ {})
        let t1 ← IO.monoMsNow
        reportAD path a (t1 - t0)
  | "anchordist" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : ADAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaAD φ a
      let t1 ← IO.monoMsNow
      reportAD s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "passhyp" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaPH φ {})
        let t1 ← IO.monoMsNow
        reportPH path a (t1 - t0)
  | "passhyp" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : PHAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaPH φ a
      let t1 ← IO.monoMsNow
      reportPH s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "cleanpass" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaCP φ {})
        let t1 ← IO.monoMsNow
        reportCP path a (t1 - t0)
  | "cleanpass" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : CPAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaCP φ a
      let t1 ← IO.monoMsNow
      reportCP s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "nested" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaNE path φ {})
        let t1 ← IO.monoMsNow
        reportNE path a (t1 - t0)
  | "nested" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : NEAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaNE s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportNE s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "nodeadm" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaNA path φ {})
        let t1 ← IO.monoMsNow
        reportNA path a (t1 - t0)
  | "nodeadm" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : NAAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaNA s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportNA s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "admtrace" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaAT path φ {})
        let t1 ← IO.monoMsNow
        reportAT path a (t1 - t0)
  | "admtrace" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : ATAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaAT s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportAT s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "mixtrace" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : MTAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaMT s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportMT s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "baddie" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaBD path φ {})
        let t1 ← IO.monoMsNow
        reportBD path a (t1 - t0)
  | "baddie" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : BDAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaBD s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportBD s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "segstep" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSS path φ {})
        let t1 ← IO.monoMsNow
        reportSS path a (t1 - t0)
  | "segstep" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SSAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSS s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "segmix" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSM path φ {})
        let t1 ← IO.monoMsNow
        reportSM path a (t1 - t0)
  | "segmix" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SMAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSM s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSM s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "segexact" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSE path φ 5000 {})
        let t1 ← IO.monoMsNow
        reportSE path a (t1 - t0)
  | "segexact" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SEAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSE s!"seed {seed} #{idx}" φ 5000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSE s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "midsym" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaMS path φ {})
        let t1 ← IO.monoMsNow
        reportMS path a (t1 - t0)
  | "midsym" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : MSAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaMS s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportMS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "roundseg" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaRS path φ true {})
        let t1 ← IO.monoMsNow
        reportRS path a (t1 - t0)
  | "roundseg" :: mode :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : RSAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaRS s!"seed {seed} #{idx}" φ (mode == "all") a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportRS s!"seed {seed} ({cases} formulas, {nvMin}+ vars, {mode})" a (t1 - t0)
  | "minreader" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaMR path φ {})
        let t1 ← IO.monoMsNow
        reportMR path a (t1 - t0)
  | "minreader" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : MRAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaMR s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportMR s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "minnode" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaMN path φ {})
        let t1 ← IO.monoMsNow
        reportMN path a (t1 - t0)
  | "minnode" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : MNAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaMN s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportMN s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "clean2" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaC2 path φ {})
        let t1 ← IO.monoMsNow
        reportC2 path a (t1 - t0)
  | "clean2" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : C2Acc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaC2 s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportC2 s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "doomed" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaDM path φ {})
        let t1 ← IO.monoMsNow
        reportDM path a (t1 - t0)
  | "doomed" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : DMAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaDM s!"seed {seed} #{idx}" φ a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportDM s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "filterkill" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaFK path φ 20 2000 {})
        let t1 ← IO.monoMsNow
        reportFK path a (t1 - t0)
  | "filterkill" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : FKAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaFK s!"seed {seed} #{idx}" φ 20 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportFK s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "cleanobl" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaCO path φ 20 2000 {})
        let t1 ← IO.monoMsNow
        reportCO path a (t1 - t0)
  | "cleanobl" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : COAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaCO s!"seed {seed} #{idx}" φ 20 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportCO s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "fullext" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaFX path φ 20 2000 {})
        let t1 ← IO.monoMsNow
        reportFX path a (t1 - t0)
  | "fullext" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : FXAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaFX s!"seed {seed} #{idx}" φ 20 2000 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportFX s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "extfire" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaEF path φ 20 200 {})
        let t1 ← IO.monoMsNow
        reportEF path a (t1 - t0)
        (← IO.getStdout).flush
  | "extfire" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : EFAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaEF s!"seed {seed} #{idx}" φ 20 200 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportEF s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "sweepcheck" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSC φ {})
        let t1 ← IO.monoMsNow
        reportSC path a (t1 - t0)
  | "sweepcheck" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SCAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSC φ a
      let t1 ← IO.monoMsNow
      reportSC s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "sweeppairs" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSP path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportSP path a (t1 - t0)
  | "sweeppairs" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SPAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSP s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSP s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "localsym" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaLS path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportLS path a (t1 - t0)
  | "localsym" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : LSAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaLS s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportLS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "midinv" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaMI φ {})
        let t1 ← IO.monoMsNow
        reportMI path a (t1 - t0)
  | "midinv" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : MIAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaMI φ a
      let t1 ← IO.monoMsNow
      reportMI s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "cleandiag" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaCD path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportCD path a (t1 - t0)
  | "cleandiag" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : CDAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaCD s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportCD s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "segops" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSGo path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportTG s!"{path} [SegGood]" a (t1 - t0)
  | "segops" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TGAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSGo s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportTG s!"seed {seed} ({cases} formulas, {nvMin}+ vars) [SegGood]" a (t1 - t0)
  | "segnodes" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSGn path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportRN s!"{path} [SegGood]" a (t1 - t0)
  | "segnodes" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : RNAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSGn s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportRN s!"seed {seed} ({cases} formulas, {nvMin}+ vars) [SegGood]" a (t1 - t0)
  | "segments" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaSG path φ 40 400 {})
        let t1 ← IO.monoMsNow
        reportSG path a (t1 - t0)
  | "segments" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SGAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaSG s!"seed {seed} #{idx}" φ 40 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportSG s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "nohostops" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaNHo path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportTG s!"{path} [SIN anfitrion]" a (t1 - t0)
  | "nohostops" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TGAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaNHo s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportTG s!"seed {seed} ({cases} formulas, {nvMin}+ vars) [SIN anfitrion]" a (t1 - t0)
  | "nohostnodes" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaNHn path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportRN s!"{path} [SIN anfitrion]" a (t1 - t0)
  | "nohostnodes" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : RNAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaNHn s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportRN s!"seed {seed} ({cases} formulas, {nvMin}+ vars) [SIN anfitrion]" a (t1 - t0)
  | "reviewnodes" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaRN path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportRN path a (t1 - t0)
  | "reviewnodes" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : RNAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaRN s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportRN s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "reviewops" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaRO path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportRO path a (t1 - t0)
  | "reviewops" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : ROAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaRO s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportRO s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "joinmix" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaJM path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportJM path a (t1 - t0)
  | "joinmix" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : JMAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaJM s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportJM s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "topgoodops" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTG path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportTG path a (t1 - t0)
  | "topgoodops" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TGAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTG s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportTG s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "upextend" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaUE path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportUE path a (t1 - t0)
  | "upextend" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : UEAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaUE s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportUE s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "chainshare" :: "file" :: paths | "chainline" :: "file" :: paths =>
    let lineToo := args.head! == "chainline"
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaCH lineToo path φ 20 400 {})
        let t1 ← IO.monoMsNow
        reportCH path a (t1 - t0)
  | "chainshare" :: "random" :: cases :: nvMin :: seeds
  | "chainline" :: "random" :: cases :: nvMin :: seeds =>
    let lineToo := args.head! == "chainline"
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : CHAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaCH lineToo s!"seed {seed} #{idx}" φ 20 400 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportCH s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "cliqueshare" :: "file" :: paths | "cliqueline" :: "file" :: paths =>
    let lineToo := args.head! == "cliqueline"
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaCS lineToo path φ 40 {})
        let t1 ← IO.monoMsNow
        reportCS path a (t1 - t0)
  | "cliqueshare" :: "random" :: cases :: nvMin :: seeds
  | "cliqueline" :: "random" :: cases :: nvMin :: seeds =>
    let lineToo := args.head! == "cliqueline"
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : CSAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaCS lineToo s!"seed {seed} #{idx}" φ 40 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportCS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "anyoption" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaAO path φ 40 {})
        let t1 ← IO.monoMsNow
        reportAO path a (t1 - t0)
  | "anyoption" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : AOAcc := {}
      let mut idx := 0
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaAO s!"seed {seed} #{idx}" φ 40 a
        idx := idx + 1
      let t1 ← IO.monoMsNow
      reportAO s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "tcsingle" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTCS φ 40 {})
        let t1 ← IO.monoMsNow
        reportTCS path a (t1 - t0)
  | "tcsingle" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TCSAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTCS φ 40 a
      let t1 ← IO.monoMsNow
      reportTCS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pairdesc" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaPD φ 40 {})
        let t1 ← IO.monoMsNow
        reportPD path a (t1 - t0)
  | "pairdesc" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : DPAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaPD φ 40 a
      let t1 ← IO.monoMsNow
      reportPD s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "roots" :: "file" :: paths | "roots-all" :: "file" :: paths =>
    let allStates := args.headD "" == "roots-all"
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaR φ allStates {})
        let t1 ← IO.monoMsNow
        reportR path a (t1 - t0)
  | "roots" :: "random" :: cases :: nvMin :: seeds
  | "roots-all" :: "random" :: cases :: nvMin :: seeds =>
    let allStates := args.headD "" == "roots-all"
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : RAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaR φ allStates a
      let t1 ← IO.monoMsNow
      reportR s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "tsread" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTS φ {})
        let t1 ← IO.monoMsNow
        reportA path a (t1 - t0)
  | "tsread" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : AAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTS φ a
      let t1 ← IO.monoMsNow
      reportA s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pinreach" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaP φ 200000 {})
        let t1 ← IO.monoMsNow
        reportP path a (t1 - t0)
  | "pinreach" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : PAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaP φ 200000 a
      let t1 ← IO.monoMsNow
      reportP s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "anc4" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaN4 φ {})
        let t1 ← IO.monoMsNow
        reportN4 path a (t1 - t0)
  | "anc4" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : N4 := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaN4 φ a
      let t1 ← IO.monoMsNow
      reportN4 s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "anc" :: "file" :: paths | "anc-all" :: "file" :: paths =>
    let allStates := args.headD "" == "anc-all"
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ =>
          if allStates then runFormulaNAll φ {} else runFormulaN φ {})
        let t1 ← IO.monoMsNow
        reportN path a (t1 - t0)
  | "anc" :: "random" :: cases :: nvMin :: seeds
  | "anc-all" :: "random" :: cases :: nvMin :: seeds =>
    let allStates := args.headD "" == "anc-all"
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : NAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := if allStates then runFormulaNAll φ a else runFormulaN φ a
      let t1 ← IO.monoMsNow
      reportN s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "sup" :: "file" :: paths | "sup-all" :: "file" :: paths =>
    let allStates := args.headD "" == "sup-all"
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ =>
          if allStates then runFormulaSAll φ 200000 {} else runFormulaS φ 200000 {})
        let t1 ← IO.monoMsNow
        reportS path a (t1 - t0)
  | "sup" :: "random" :: cases :: nvMin :: seeds
  | "sup-all" :: "random" :: cases :: nvMin :: seeds =>
    let allStates := args.headD "" == "sup-all"
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : SAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := if allStates then runFormulaSAll φ 200000 a else runFormulaS φ 200000 a
      let t1 ← IO.monoMsNow
      reportS s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "join" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaJ φ {})
        let t1 ← IO.monoMsNow
        reportJ path a (t1 - t0)
  | "join" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : JAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaJ φ a
      let t1 ← IO.monoMsNow
      reportJ s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "bt" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaBT φ {})
        let t1 ← IO.monoMsNow
        reportBT path a (t1 - t0)
  | "bt" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : BAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaBT φ a
      let t1 ← IO.monoMsNow
      reportBT s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pm" :: "file" :: paths =>
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaPM φ {})
        let t1 ← IO.monoMsNow
        reportPM path a (t1 - t0)
  | "traj" :: "file" :: paths | "traj-sib" :: "file" :: paths | "traj-top" :: "file" :: paths =>
    let sibs := args.headD "" == "traj-sib"
    let topDown := args.headD "" == "traj-top"
    for path in paths do
      match ← loadCnf path with
      | none => IO.println s!"{path}: bad cnf"
      | some φ =>
        let t0 ← IO.monoMsNow
        let a ← IO.lazyPure (fun _ => runFormulaTraj topDown sibs φ {})
        let t1 ← IO.monoMsNow
        reportTraj path a (t1 - t0)
  | "traj" :: "random" :: cases :: nvMin :: seeds
  | "traj-sib" :: "random" :: cases :: nvMin :: seeds
  | "traj-top" :: "random" :: cases :: nvMin :: seeds =>
    let sibs := args.headD "" == "traj-sib"
    let topDown := args.headD "" == "traj-top"
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : TAcc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaTraj topDown sibs φ a
      let t1 ← IO.monoMsNow
      reportTraj s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "pm" :: "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : Acc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormulaPM φ a
      let t1 ← IO.monoMsNow
      reportPM s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | "random" :: cases :: nvMin :: seeds =>
    for seed in seeds.map String.toNat! do
      let t0 ← IO.monoMsNow
      let mut a : Acc := {}
      for φ in randomCnfs cases.toNat! nvMin.toNat! seed do
        a := runFormula φ a
      let t1 ← IO.monoMsNow
      report s!"seed {seed} ({cases} formulas, {nvMin}+ vars)" a (t1 - t0)
  | _ =>
    IO.println "usage: row-degree [pm|bt|join|traj|traj-sib|traj-top] file <cnf>... | row-degree [pm|traj|traj-sib|traj-top] random <cases> <minVars> <seed>..."
