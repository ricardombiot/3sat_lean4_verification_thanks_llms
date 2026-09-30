-- lean/improves_bingo/AbsSatBingo/Model/ForbidOn.lean
import AbsSatBingo.Model.Driver

/-!
# La máquina con `FORBID = :on` (`docs/plans/lean_forbid_on.md`, F1)

Espejo computable de los tríos prohibidos de Julia (`55ddcc3`):

| Julia | Lean |
|---|---|
| `dead_trio(g, a, b, r)` (`r ∈ forbid(a–b)`) | `deadTrio` (la arista `a–b` y el trío en `trios`) |
| `forbid!(g, a, b, r)` | `forbidTrio` |
| `side_forbids(g, a, b, r)` | `sideForbidsB` |
| `up_forbid!(g, n, parents)` tras `create_from_parents!` | `upForbidNode`, `upForbidRow` |
| `join_forbid(ga, gb)` + `set_forbid!` en `union!` | `joinForbid`, `joinOn` |
| `good_witness`, `trio_alive`, `edge_alive` | `goodWitnessB`, `trioAlive`, `edgeAlive` |
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
-- UP (Julia up_forbid!)
-- ============================================================

/-- Los vecinos de `n` (Julia `neighbors_all` sin `n`). -/
def nbrs (g : GPathB) (n : PathNodeId) : List PathNodeId :=
  g.alive.filter (fun w => w != n && g.hasEdge n w)

/-- Las parejas `(w, r)`, `w` antes que `r` en la lista. -/
def pairsOf : List PathNodeId → List (PathNodeId × PathNodeId)
  | [] => []
  | w :: ws => ws.map (fun r => (w, r)) ++ pairsOf ws

/-- Julia `up_forbid!`: `(n, w, r)` se prohíbe si todo padre `p` de `n` corta `(p, w, r)`. Las parejas se deciden
contra el estado de antes (Julia las junta y después escribe). -/
def upForbidNode (g : GPathB) (n : PathNodeId) (parents : List PathNodeId) : GPathB :=
  let todo := (pairsOf (g.nbrs n)).filter (fun wr =>
    g.hasEdge wr.1 wr.2 && parents.all (fun p => g.sideForbidsB p wr.1 wr.2))
  todo.foldl (fun h wr => h.forbidTrio n wr.1 wr.2) g

/-- Los padres de un nodo de la fila (los de su documento). -/
def parentsOf (g : GPathB) (n : PathNodeId) : List PathNodeId :=
  match g.node? n with
  | some m => m.parents
  | none => []

/-- `up_forbid!` para cada nodo de la fila nueva. Los nodos de una fila no son vecinos entre sí y sus padres son
viejos, así que el orden no cambia nada. -/
def upForbidRow (g : GPathB) (ids : List PathNodeId) : GPathB :=
  ids.foldl (fun h n => h.upForbidNode n (h.parentsOf n)) g

-- ============================================================
-- join (Julia join_forbid + set_forbid!)
-- ============================================================

/-- Julia `join_forbid`, con los dos lados antes de unir: por cada arista `a–b` de un lado, los `r` vecinos de `a`
en algún lado, con `b–r` en algún lado, que los dos lados cortan. -/
def joinForbid (g₁ g₂ : GPathB) : List (PathNodeId × PathNodeId × PathNodeId) :=
  (g₁.edges ++ g₂.edges).flatMap (fun e =>
    ((g₁.alive ++ g₂.alive).filter (fun r =>
      r != e.1 && r != e.2 && (g₁.hasEdge e.1 r || g₂.hasEdge e.1 r) &&
      (g₁.hasEdge e.2 r || g₂.hasEdge e.2 r) &&
      g₁.sideForbidsB e.1 e.2 r && g₂.sideForbidsB e.1 e.2 r)).map (fun r => (e.1, e.2, r)))

/-- Julia `union!` con `FORBID = :on`: la unión, con los tríos reiniciados a los de `join_forbid`. -/
def joinOn (g₁ g₂ : GPathB) : GPathB :=
  (joinForbid g₁ g₂).foldl (fun h t => h.forbidTrio t.1 t.2.1 t.2.2) { join g₁ g₂ with trios := [] }

def doJoinOn (g₁ g₂ : GPathB) : GPathB :=
  if okJoin g₁ g₂ then joinOn g₁ g₂ else g₁

-- ============================================================
-- La regla (Julia forbid_rule!)
-- ============================================================

/-- Los vecinos de `a` en el paso `l`, con `a` mismo en el suyo (Julia `g.inc[a][l]`). -/
def incAt (g : GPathB) (a : PathNodeId) (l : Int) : List PathNodeId :=
  g.alive.filter (fun s => s.id.step == l && g.adjb a s)

/-- Julia `good_witness`. -/
def goodWitnessB (g : GPathB) (a b r s : PathNodeId) : Bool :=
  s == a || s == b || s == r ||
  (g.hasEdge a s && g.hasEdge b s && g.hasEdge r s &&
   !g.deadTrio a b s && !g.deadTrio a r s && !g.deadTrio b r s)

/-- Julia `trio_alive`: en cada paso, un testigo bueno entre los vecinos de `a`. -/
def trioAlive (g : GPathB) (a b r : PathNodeId) : Bool :=
  (intRange 0 (g.current_step - 1)).all (fun l => (g.incAt a l).any (g.goodWitnessB a b r))

/-- Julia `edge_alive`: en cada paso, un vecino de `a` que lo es de `b` sin trío prohibido. -/
def edgeAlive (g : GPathB) (a b : PathNodeId) : Bool :=
  (intRange 0 (g.current_step - 1)).all (fun l =>
    (g.incAt a l).any (fun r => r == a || r == b || (g.hasEdge b r && !g.deadTrio a b r)))

/-- Fase 1: los triángulos sin prohibir y sin testigo bueno en algún paso, decididos contra el mismo estado. -/
def newTrios (g : GPathB) : List (PathNodeId × PathNodeId × PathNodeId) :=
  g.edges.flatMap (fun e =>
    (g.alive.filter (fun r =>
      r != e.1 && r != e.2 && g.hasEdge e.1 r && g.hasEdge e.2 r &&
      !g.deadTrio e.1 e.2 r && !g.trioAlive e.1 e.2 r)).map (fun r => (e.1, e.2, r)))

/-- Una vuelta de `forbid_rule!`: fase 1 (tríos), fase 2 (aristas sin testigo bueno, todas a la vez; si quita alguna,
`dirty` y la limpieza). Devuelve el estado y si cambió algo. -/
def forbidRound (g : GPathB) : GPathB × Bool :=
  let g₁ := g.newTrios.foldl (fun h t => h.forbidTrio t.1 t.2.1 t.2.2) g
  let grew := decide (g.trios.length < g₁.trios.length)
  let bad := g₁.edges.filter (fun e => !g₁.edgeAlive e.1 e.2)
  if bad.isEmpty then (g₁, grew)
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
