-- lean/improves_bingo/AbsSatBingo/Model/ForbidOn.lean
import AbsSatBingo.Model.Driver

/-!
# La máquina con `FORBID = :on` (`docs/plans/lean_forbid_on.md`, F1)

Espejo computable de los tríos prohibidos de Julia (`55ddcc3`):

| Julia | Lean |
|---|---|
| `dead_trio(g, a, b, r)` (`r ∈ forbid(a–b)`) | `deadTrio` (la arista `a–b` y el trío en `trios`); en tabla hash, `Idx.deadTrio` |
| `forbid!(g, a, b, r)` | `forbidTrio` |
| `side_forbids(g, a, b, r)` | `sideForbidsB` |
| `up_forbid!(g, n, parents)` tras `create_from_parents!` | `upForbidTodo`, `upForbidRow` |
| `join_forbid(ga, gb)` + `set_forbid!` en `union!` | `joinForbid`, `joinOn` |
| `good_witness`, `trio_alive`, `edge_alive` | `Idx.goodWitness`, `Idx.trioAlive`, `Idx.edgeAlive` |
| `forbid_rule!` (dos fases, hasta que no cambia nada) | `forbidRound`, `forbidRule` |
| `make_review_owners!`: limpieza, parejas, **regla**, enlaces, padres/hijos, enlaces | `reviewPassOn`, `reviewOn` |

**El modo** (`Mode`): cada operación de la máquina recibe `.off` o `.on`. Con `.off` es, por definición, la de
siempre (`reviewM_off`, `advanceM_off`, …: `rfl`), así que ningún teorema existente cambia.

**Tríos en las aristas.** Julia escribe `(a, b, r)` en las tres aristas del trío a la vez. Una arista borrada no
vuelve con su `forbid` viejo: el UP solo crea aristas con el nodo nuevo, y el join los reinicia todos. Por eso
«`r ∈ forbid(a–b)` en Julia» es «la arista `a–b` existe y el trío `{a, b, r}` se escribió desde el último join», que es
`deadTrio`. Las consultas de Julia solo miran tríos cuyas aristas existen.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

/-- El modo de los tríos prohibidos (Julia `PathOwnersGraph.FORBID`). -/
inductive Mode where
  | off
  | on
  deriving DecidableEq, Repr

namespace GPathB

-- ============================================================
-- Tríos: consulta y escritura
-- ============================================================

/-- `t` es el trío `{a, b, r}`, en cualquier orden. -/
def trioIs (a b r : PathNodeId) (t : PathNodeId × PathNodeId × PathNodeId) : Bool :=
  (t.1 == a && t.2.1 == b && t.2.2 == r) || (t.1 == a && t.2.1 == r && t.2.2 == b) ||
  (t.1 == b && t.2.1 == a && t.2.2 == r) || (t.1 == b && t.2.1 == r && t.2.2 == a) ||
  (t.1 == r && t.2.1 == a && t.2.2 == b) || (t.1 == r && t.2.1 == b && t.2.2 == a)

/-- Julia `dead_trio`: `r ∈ forbid(a–b)`. -/
def deadTrio (g : GPathB) (a b r : PathNodeId) : Bool :=
  g.hasEdge a b && g.trios.any (trioIs a b r)

/-- Julia `forbid!`: escribe el trío si no lo estaba. -/
def forbidTrio (g : GPathB) (a b r : PathNodeId) : GPathB :=
  if g.deadTrio a b r then g else { g with trios := g.trios ++ [(a, b, r)] }

/-- Julia `side_forbids`: no hay solución por `a`, `b` y `r` (falta una de las tres posesiones, o el trío está
prohibido). Con `a = b`, o `r` igual a uno de los dos, basta la posesión. -/
def sideForbidsB (g : GPathB) (a b r : PathNodeId) : Bool :=
  if !(g.adjb a b && g.adjb a r && g.adjb b r) then true
  else if a == b || r == a || r == b then false
  else g.deadTrio a b r

-- ============================================================
-- El índice de un estado (las consultas de Julia, en tablas hash)
-- ============================================================

/-- Las seis ordenaciones de un trío. -/
def perms (a b r : PathNodeId) : List (PathNodeId × PathNodeId × PathNodeId) :=
  [(a, b, r), (a, r, b), (b, a, r), (b, r, a), (r, a, b), (r, b, a)]

/-- **El índice de un estado**, construido una vez y consultado muchas: aristas en las dos orientaciones, tríos en
sus seis órdenes, vivos y vecinos por nodo (Julia `edges`, `forbid`, `alive`, `inc`). Las decisiones de cada regla se
toman contra un mismo estado, así que un índice por estado basta. Cada consulta es la de listas de arriba
(`deadTrio`, `sideForbidsB`, …); las igualdades son de F3. -/
structure Idx where
  edges : Std.HashSet (PathNodeId × PathNodeId)
  trios : Std.HashSet (PathNodeId × PathNodeId × PathNodeId)
  alive : Std.HashSet PathNodeId
  nbr   : Std.HashMap PathNodeId (List PathNodeId)
  cs    : Int

def Idx.of (g : GPathB) : Idx :=
  { edges := g.edges.foldl (fun h e => (h.insert (e.1, e.2)).insert (e.2, e.1)) {},
    trios := g.trios.foldl (fun h t => h.insertMany (perms t.1 t.2.1 t.2.2)) {},
    alive := g.alive.foldl (fun h x => h.insert x) {},
    nbr := g.edges.foldl (fun m e =>
      (m.insert e.1 (e.2 :: m.getD e.1 [])).insert e.2 (e.1 :: (m.insert e.1 (e.2 :: m.getD e.1 [])).getD e.2 [])) {},
    cs := g.current_step }

namespace Idx

def hasEdge (i : Idx) (a b : PathNodeId) : Bool := i.edges.contains (a, b)

def deadTrio (i : Idx) (a b r : PathNodeId) : Bool := i.hasEdge a b && i.trios.contains (a, b, r)

def adjb (i : Idx) (x w : PathNodeId) : Bool := (x == w && i.alive.contains x) || i.hasEdge x w

def sideForbids (i : Idx) (a b r : PathNodeId) : Bool :=
  if !(i.adjb a b && i.adjb a r && i.adjb b r) then true
  else if a == b || r == a || r == b then false
  else i.deadTrio a b r

/-- Los vecinos vivos de `a` (sin `a`). -/
def nbrs (i : Idx) (a : PathNodeId) : List PathNodeId :=
  (i.nbr.getD a []).filter (fun s => s != a && i.alive.contains s)

/-- Julia `g.inc[a][l]`: los vecinos de `a` en el paso `l`, con `a` en el suyo. -/
def incAt (i : Idx) (a : PathNodeId) (l : Int) : List PathNodeId :=
  (if a.id.step == l && i.alive.contains a then [a] else []) ++ (i.nbrs a).filter (fun s => s.id.step == l)

def goodWitness (i : Idx) (a b r s : PathNodeId) : Bool :=
  s == a || s == b || s == r ||
  (i.hasEdge a s && i.hasEdge b s && i.hasEdge r s &&
   !i.deadTrio a b s && !i.deadTrio a r s && !i.deadTrio b r s)

def trioAlive (i : Idx) (a b r : PathNodeId) : Bool :=
  (intRange 0 (i.cs - 1)).all (fun l => (i.incAt a l).any (i.goodWitness a b r))

def edgeAlive (i : Idx) (a b : PathNodeId) : Bool :=
  (intRange 0 (i.cs - 1)).all (fun l =>
    (i.incAt a l).any (fun r => r == a || r == b || (i.hasEdge b r && !i.deadTrio a b r)))

end Idx

/-- Añade tríos que no están escritos, sin repetir (Julia `forbid!` uno a uno: el segundo de un mismo trío ya lo
encuentra prohibido). `i` es el índice del estado al que se añaden. -/
def addTrios (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId)) : GPathB × Bool :=
  let r := ts.foldl (fun (acc : List (PathNodeId × PathNodeId × PathNodeId) ×
      Std.HashSet (PathNodeId × PathNodeId × PathNodeId)) t =>
    if acc.2.contains t || i.deadTrio t.1 t.2.1 t.2.2 then acc
    else (t :: acc.1, acc.2.insertMany (perms t.1 t.2.1 t.2.2))) ([], {})
  ({ g with trios := g.trios ++ r.1.reverse }, !r.1.isEmpty)

-- ============================================================
-- UP (Julia up_forbid!)
-- ============================================================

/-- Las parejas `(w, r)`, `w` antes que `r` en la lista. -/
def pairsOf : List PathNodeId → List (PathNodeId × PathNodeId)
  | [] => []
  | w :: ws => ws.map (fun r => (w, r)) ++ pairsOf ws

/-- Los padres de un nodo de la fila (los de su documento). -/
def parentsOf (g : GPathB) (n : PathNodeId) : List PathNodeId :=
  match g.node? n with
  | some m => m.parents
  | none => []

/-- Julia `up_forbid!` para un nodo nuevo `n`: `(n, w, r)` si todo padre `p` de `n` corta `(p, w, r)`. -/
def upForbidTodo (i : Idx) (n : PathNodeId) (parents : List PathNodeId) :
    List (PathNodeId × PathNodeId × PathNodeId) :=
  ((pairsOf (i.nbrs n)).filter (fun wr =>
    i.hasEdge wr.1 wr.2 && parents.all (fun p => i.sideForbids p wr.1 wr.2))).map (fun wr => (n, wr.1, wr.2))

/-- `up_forbid!` para cada nodo de la fila nueva, contra el estado tras la fila: los nodos de una fila no son vecinos
entre sí y sus padres son viejos, así que lo que escribe uno no cambia lo que decide otro. -/
def upForbidRow (g : GPathB) (ids : List PathNodeId) : GPathB :=
  let i := Idx.of g
  (g.addTrios i (ids.flatMap (fun n => upForbidTodo i n (g.parentsOf n)))).1

-- ============================================================
-- join (Julia join_forbid + set_forbid!)
-- ============================================================

/-- Julia `join_forbid`, con los dos lados antes de unir: por cada arista `a–b` de un lado, los `r` vecinos de `a`
en algún lado, con `b–r` en algún lado, que los dos lados cortan. -/
def joinForbid (g₁ g₂ : GPathB) : List (PathNodeId × PathNodeId × PathNodeId) :=
  let i₁ := Idx.of g₁
  let i₂ := Idx.of g₂
  (g₁.edges ++ g₂.edges).flatMap (fun e =>
    ((i₁.nbrs e.1 ++ i₂.nbrs e.1).filter (fun r =>
      r != e.2 && (i₁.hasEdge e.2 r || i₂.hasEdge e.2 r) &&
      i₁.sideForbids e.1 e.2 r && i₂.sideForbids e.1 e.2 r)).map (fun r => (e.1, e.2, r)))

/-- Julia `union!` con `FORBID = :on`: la unión, con los tríos reiniciados a los de `join_forbid`. -/
def joinOn (g₁ g₂ : GPathB) : GPathB :=
  let u : GPathB := { join g₁ g₂ with trios := [] }
  (u.addTrios (Idx.of u) (joinForbid g₁ g₂)).1

def doJoinOn (g₁ g₂ : GPathB) : GPathB :=
  if okJoin g₁ g₂ then joinOn g₁ g₂ else g₁

-- ============================================================
-- La regla (Julia forbid_rule!)
-- ============================================================

/-- Fase 1: los triángulos sin prohibir y sin testigo bueno en algún paso, decididos contra el mismo estado. -/
def newTrios (g : GPathB) (i : Idx) : List (PathNodeId × PathNodeId × PathNodeId) :=
  g.edges.flatMap (fun e =>
    ((i.nbrs e.1).filter (fun r =>
      r != e.2 && i.hasEdge e.2 r && !i.deadTrio e.1 e.2 r && !i.trioAlive e.1 e.2 r)).map (fun r => (e.1, e.2, r)))

/-- Una vuelta de `forbid_rule!`: fase 1 (tríos), fase 2 (aristas sin testigo bueno, todas a la vez; si quita alguna,
`dirty` y la limpieza). Devuelve el estado y si cambió algo. -/
def forbidRound (g : GPathB) : GPathB × Bool :=
  let i := Idx.of g
  let r₁ := g.addTrios i (g.newTrios i)
  let g₁ := r₁.1
  let i₁ := Idx.of g₁
  let bad := g₁.edges.filter (fun e => !i₁.edgeAlive e.1 e.2)
  if bad.isEmpty then (g₁, r₁.2)
  else (clean { bad.foldl (fun h e => h.removeEdge e.1 e.2) g₁ with dirty := true }, true)

/-- Vueltas mientras el estado es válido y la anterior cambió algo. -/
def forbidFuel : Nat → GPathB → GPathB
  | 0, g => g
  | fuel + 1, g =>
    if g.isValid then
      let r := g.forbidRound
      if r.2 then forbidFuel fuel r.1 else r.1
    else g

/-- Tope de vueltas: cada una que sigue escribe un trío (hay a lo sumo vivos³) o quita algo (`measure`). -/
def forbidBound (g : GPathB) : Nat :=
  g.alive.length ^ 3 + g.measure + 1

/-- **Julia `forbid_rule!`.** -/
def forbidRule (g : GPathB) : GPathB :=
  forbidFuel g.forbidBound g

-- ============================================================
-- El review con la regla (Julia make_review_owners! con FORBID = :on)
-- ============================================================

/-- Una vuelta: limpieza y parejas, **la regla**, enlaces, pasadas, enlaces. -/
def reviewPassOn (g : GPathB) : GPathB :=
  g.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons.pruneLinks

def reviewFuelOn : Nat → GPathB → GPathB
  | 0, g => g
  | fuel + 1, g =>
    if g.isValid && g.dirty then
      let p := reviewPassOn { g with dirty := false }
      if p.dirty then reviewFuelOn fuel p
      else if p.isValid then
        let f := finalPass p
        if f.dirty then reviewFuelOn fuel f else p
      else p
    else g

def reviewOn (g : GPathB) : GPathB :=
  reviewFuelOn (g.measure + 1) g

def filterAllOn (g : GPathB) (reqs : List NodeId) : GPathB :=
  reviewOn (reqs.foldl filterRequire g)

/-- Julia `do_up!` con `FORBID = :on`: la fila (conserva los tríos), `up_forbid!` por nodo y, si hace falta, el
review. -/
def upOn (g : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : GPathB :=
  if g.isValid then
    reviewOn (upForbidRow { g.addNode d title forb with trios := g.trios } (g.newRowIds d forb))
  else g

def upFilteringOn (g : GPathB) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) : GPathB :=
  upOn (g.filterAllOn reqs) d title forb

def initSeedOn (d : NodeId) (title : String) : GPathB :=
  upOn empty d title (fun _ => false)

-- ============================================================
-- Las operaciones con modo
-- ============================================================

def reviewM : Mode → GPathB → GPathB
  | .off => review
  | .on => reviewOn

def filterAllM : Mode → GPathB → List NodeId → GPathB
  | .off => filterAll
  | .on => filterAllOn

def upFilteringM : Mode → GPathB → List NodeId → NodeId → String → (PathNodeId → Bool) → GPathB
  | .off => upFiltering
  | .on => upFilteringOn

def doJoinM : Mode → GPathB → GPathB → GPathB
  | .off => doJoin
  | .on => doJoinOn

def initSeedM : Mode → NodeId → String → GPathB
  | .off => initSeed
  | .on => initSeedOn

theorem reviewM_off : reviewM .off = review := rfl
theorem filterAllM_off : filterAllM .off = filterAll := rfl
theorem upFilteringM_off : upFilteringM .off = upFiltering := rfl
theorem doJoinM_off : doJoinM .off = doJoin := rfl
theorem initSeedM_off : initSeedM .off = initSeed := rfl

end GPathB

-- ============================================================
-- La máquina con modo
-- ============================================================

namespace Driver

open GPathB

def insertM (m : Mode) (line : Line) (key : NodeId) (g : GPathB) : Line :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) => line.map (fun kv => if kv.1 == key then (key, doJoinM m existing g) else kv)
  | none => line ++ [(key, g)]

def sendToM (m : Mode) (φ : Cnf) (g : GPathB) (next : Line) (d : NodeId) : Line :=
  let g' := upFilteringM m g (reqOf φ d) d "" (isProhibited φ)
  if g'.isValid then insertM m next d g' else next

def sendAllM (m : Mode) (φ : Cnf) (kv : NodeId × GPathB) (next : Line) : Line :=
  (sonsOfMap φ kv.1).foldl (sendToM m φ kv.2) next

def advanceM (m : Mode) (φ : Cnf) (line : Line) : Line :=
  line.foldl (fun next kv => sendAllM m φ kv next) []

def initM (m : Mode) (φ : Cnf) : Line :=
  (mapNodes φ 0).foldl (fun line id => insertM m line id (initSeedM m id "")) []

def stepsM (m : Mode) (φ : Cnf) : Nat → Line → Line
  | 0, line => line
  | n + 1, line => stepsM m φ n (advanceM m φ line)

def runM (m : Mode) (φ : Cnf) : Line := stepsM m φ (stepCount φ - 1).toNat (initM m φ)

def machineVerdictM (m : Mode) (φ : Cnf) : Bool := !(runM m φ).isEmpty

theorem insertM_off : insertM .off = insert := rfl
theorem sendToM_off : sendToM .off = sendTo := rfl
theorem sendAllM_off : sendAllM .off = sendAll := rfl
theorem advanceM_off : advanceM .off = advance := rfl
theorem initM_off : initM .off = init := rfl

theorem stepsM_off (φ : Cnf) : ∀ n line, stepsM .off φ n line = steps φ n line := by
  intro n
  induction n with
  | zero => intro line; rfl
  | succ n ih => intro line; exact ih _

theorem runM_off (φ : Cnf) : runM .off φ = run φ := stepsM_off φ _ _
theorem machineVerdictM_off (φ : Cnf) : machineVerdictM .off φ = machineVerdict φ := by
  unfold machineVerdictM machineVerdict; rw [runM_off]

end Driver

end AbsSatBingo.Model
