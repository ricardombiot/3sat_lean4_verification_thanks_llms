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
