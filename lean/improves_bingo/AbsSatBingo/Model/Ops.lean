-- lean/improves_bingo/AbsSatBingo/Model/Ops.lean
import AbsSatBingo.Model.GPathB

/-!
# Las operaciones de la máquina sobre `GPathB`

Fase L2 de `docs/plans/lean_bingo.md`: espejo de `julia/improves_bingo/src/graph_path/` (UP, filtro, review,
join). Cada función dice de qué función de Julia es espejo. Las diferencias a propósito:

* **El orden de los recorridos.** Julia recorre `Dict`s y `Set`s en orden de hash; aquí, el orden de las listas.
  En los estados válidos no cambia el resultado: la purga llega al mismo punto fijo en cualquier orden, la regla de
  parejas decide todas las aristas contra el mismo estado, y en las pasadas dos nodos de una misma línea no son
  vecinos (L5 lo convierte en lema). Los estados inválidos se descartan en los dos lados.
* **La regla de parejas** mira cada paso por debajo de `current_step` (`pairOk`); Julia mira los pasos donde los
  dos tienen línea en la incidencia. Tras la purga coinciden: un nodo vivo tiene un vecino vivo en cada paso.
* **Terminación por combustible**, como en `GPathM`: cada vuelta que sigue ha borrado algo (`measure` baja). Los
  lemas de suficiencia del combustible son de L5.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids)

namespace GPathB

-- ============================================================
-- Filtro por requisito (Julia filter_require!)
-- ============================================================

/-- Fija `req` como el único nodo de mapa visitable de su paso: los nodos de camino de ese paso que están por
otro nodo de mapa salen del grafo de owners (`killVertex`); su documento queda hasta la purga. -/
def filterRequire (g : GPathB) (req : NodeId) : GPathB :=
  if g.isValid then
    let victims := ((g.line req.step).map (·.id)).filter (fun q => q.id != req)
    let g' := victims.foldl killVertex g
    { g' with dirty := g'.dirty || !victims.isEmpty }
  else g

-- ============================================================
-- La purga (Julia clean_invalid_nodes!)
-- ============================================================

/-- Elimina el nodo si ya no es válido. -/
def purgeStep (g : GPathB) (id : PathNodeId) : GPathB :=
  match g.node? id with
  | none => g
  | some n => if g.isValidNode n then g else { g.removeNode id with dirty := true }

def purgeRound (g : GPathB) : GPathB :=
  (g.nodes.map (·.id)).foldl purgeStep g

/-- Vueltas de purga mientras el gpath es válido y la vuelta elimina algo. -/
def purgeFuel : Nat → GPathB → GPathB
  | 0, g => g
  | fuel + 1, g =>
    if g.isValid then
      let g' := g.purgeRound
      if g'.nodes.length < g.nodes.length then purgeFuel fuel g' else g'
    else g

/-- **La purga**: hasta que no se elimina nada. Sin segunda fase: al eliminar un nodo se van sus aristas. -/
def clean (g : GPathB) : GPathB :=
  purgeFuel (g.nodes.length + 1) g

-- ============================================================
-- La regla de parejas (Julia pair_consistency_after_clean!)
-- ============================================================

/-- `x` y `w` tienen un vecino vivo común en el paso `k`. -/
def commonAt (g : GPathB) (x w : PathNodeId) (k : Int) : Bool :=
  g.alive.any (fun z => z.id.step == k && g.adjb x z && g.adjb w z)

/-- La arista (`x`,`w`) comparte vecino en cada paso (Julia `shares_every_step`). -/
def pairOk (g : GPathB) (x w : PathNodeId) : Bool :=
  (intRange 0 (g.current_step - 1)).all (g.commonAt x w)

/-- Una vuelta de la regla: todas las aristas malas, decididas contra el mismo estado, se quitan a la vez. -/
def pairSweep (g : GPathB) : GPathB × Bool :=
  let bad := g.edges.filter (fun e => !g.pairOk e.1 e.2)
  (bad.foldl (fun h e => h.removeEdge e.1 e.2) g, !bad.isEmpty)

/-- Regla y purga mientras la regla quita algo. -/
def pairFuel : Nat → GPathB → GPathB
  | 0, g => g
  | fuel + 1, g =>
    if g.isValid then
      let r := g.pairSweep
      if r.2 then pairFuel fuel (clean { r.1 with dirty := true }) else g
    else g

/-- La purga y después la regla de parejas hasta su punto fijo. -/
def cleanPair (g : GPathB) : GPathB :=
  let g₀ := g.clean
  pairFuel (g₀.measure + 1) g₀

-- ============================================================
-- Enlaces caducados (Julia prune_stale_links!)
-- ============================================================

/-- El enlace de `a` a `b` sigue en pie: `b` existe y se poseen. -/
def linkOk (g : GPathB) (a b : PathNodeId) : Bool :=
  (g.node? b).isSome && g.adjb a b

/-- Quita los enlaces entre dos nodos que ya no se poseen, en los dos lados a la vez (la condición es simétrica). -/
def pruneLinks (g : GPathB) : GPathB :=
  if g.isValid then
    let nodes := g.nodes.map (fun n =>
      { n with parents := n.parents.filter (g.linkOk n.id), sons := n.sons.filter (g.linkOk n.id) })
    let changed := decide ((nodes.map PNodeB.weight).sum < (g.nodes.map PNodeB.weight).sum)
    { g with nodes := nodes, dirty := g.dirty || changed }
  else g

-- ============================================================
-- Las pasadas de padres e hijos (Julia review_owners_parents_sons! / _sons_parents!)
-- ============================================================

/-- El corte de la tabla de `x` (Julia `cut_by_support!`): se quita la arista (`x`,`w`) si ningún nodo de `sup`
posee a `w`. -/
def cutSupport (g : GPathB) (x : PathNodeId) (sup : List PathNodeId) : GPathB × Bool :=
  let drop := g.alive.filter (fun w => w != x && g.adjb x w && !sup.any (fun p => g.adjb p w))
  (drop.foldl (fun h w => h.removeEdge x w) g, !drop.isEmpty)

/-- Un nodo de una pasada: si es válido, su corte; después, fuera si ya no es válido. -/
def reviewNode (sel : PNodeB → List PathNodeId) (g : GPathB) (id : PathNodeId) : GPathB :=
  match g.node? id with
  | none => g
  | some n =>
    let g :=
      if g.isValidNode n then
        let r := g.cutSupport id (sel n)
        if r.2 then { r.1 with dirty := true } else r.1
      else g
    -- el corte solo quita aristas: el documento de `n` es el mismo
    if g.isValidNode n then g else { g.removeNode id with dirty := true }

def reviewLine (sel : PNodeB → List PathNodeId) (g : GPathB) (k : Int) : GPathB :=
  ((g.line k).map (·.id)).foldl (reviewNode sel) g

/-- Recorre los pasos y se para en cuanto el gpath deja de ser válido (el `break` de Julia). -/
def reviewSteps (sel : PNodeB → List PathNodeId) (g : GPathB) : List Int → GPathB
  | [] => g
  | k :: ks =>
    let g := reviewLine sel g k
    if g.isValid then reviewSteps sel g ks else g

/-- De arriba abajo: pasos `1 … current_step-1`, contra los padres. Solo si hay algo que revisar. -/
def reviewParents (g : GPathB) : GPathB :=
  if g.isValid && g.dirty then reviewSteps (·.parents) g (intRange 1 (g.current_step - 1)) else g

/-- De abajo arriba: pasos `current_step-2 … 0`, contra los hijos. -/
def reviewSons (g : GPathB) : GPathB :=
  if g.isValid && g.dirty then reviewSteps (·.sons) g (intRange 0 (g.current_step - 2)).reverse else g

-- ============================================================
-- El review (Julia make_review_owners!)
-- ============================================================

/-- Una vuelta: purga, parejas, enlaces, pasadas, enlaces. -/
def reviewPass (g : GPathB) : GPathB :=
  g.cleanPair.pruneLinks.reviewParents.reviewSons.pruneLinks

/-- Vueltas mientras el gpath es válido y algo cambió en la anterior. -/
def reviewFuel : Nat → GPathB → GPathB
  | 0, g => g
  | fuel + 1, g =>
    if g.isValid && g.dirty then reviewFuel fuel (reviewPass { g with dirty := false }) else g

def review (g : GPathB) : GPathB :=
  reviewFuel (g.measure + 1) g

/-- Julia `filter!`: los requisitos y, si algo cambió, el review. -/
def filterAll (g : GPathB) (reqs : List NodeId) : GPathB :=
  review (reqs.foldl filterRequire g)

-- ============================================================
-- El UP (Julia add_row! / do_up! / do_up_filtering!)
-- ============================================================

/-- Los ids de la última fila: los padres candidatos de la fila nueva. -/
def newParents (g : GPathB) : List PathNodeId :=
  if g.current_step > 0 then (g.line (g.current_step - 1)).map (·.id) else []

/-- Los ids candidatos de la fila (Julia `group_parents_by_shifted_id`): uno por cada id que el
desplazamiento de la ventana da a la última fila; antes de nada, la raíz. -/
def shiftRowIds (g : GPathB) (d : NodeId) : List PathNodeId :=
  if g.current_step > 0 then dedupPids ((g.newParents).map (fun q => shiftPid q d))
  else [{ id := d, parent_id := none, gparent_id := none }]

/-- Los ids de la fila que se crea: los candidatos no prohibidos. -/
def newRowIds (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) : List PathNodeId :=
  (g.shiftRowIds d).filter (fun pid => !forb pid)

/-- Algún candidato estaba prohibido: Julia activa `review_owners`. -/
def skipsWindow (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) : Bool :=
  (g.shiftRowIds d).any forb

/-- Los padres de un nodo de la fila: los de la última fila que se desplazan a su id. -/
def rowParents (g : GPathB) (d : NodeId) (pid : PathNodeId) : List PathNodeId :=
  g.newParents.filter (fun q => shiftPid q d == pid)

/-- Los vecinos de un nodo de la fila (Julia `create_from_parents!`): los vivos de pasos anteriores que posee
alguno de sus padres. Un hermano nunca entra: está en el paso del propio nodo. -/
def rowNeighbors (g : GPathB) (d : NodeId) (pid : PathNodeId) : List PathNodeId :=
  g.alive.filter (fun w => decide (w.id.step < pid.id.step) && (g.rowParents d pid).any (fun p => g.adjb p w))

def rowNode (g : GPathB) (d : NodeId) (title : String) (pid : PathNodeId) : PNodeB :=
  { id := pid, title := title, parents := g.rowParents d pid, sons := [] }

/-- Los ids de la fila de los que un nodo viejo pasa a ser padre. -/
def gainedSons (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) (n : PNodeB) : List PathNodeId :=
  (g.newRowIds d forb).filter (fun pid => (g.rowParents d pid).contains n.id)

/-- **La fila nueva** (Julia `add_row!`): un nodo por id no prohibido, sus enlaces y sus aristas. Una fila vacía
deja el paso nuevo sin vivos, así que `isValid` falla solo. -/
def addNode (g : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : GPathB :=
  let ids := g.newRowIds d forb
  { nodes := g.nodes.map (fun n => { n with sons := n.sons ++ g.gainedSons d forb n }) ++
      ids.map (g.rowNode d title),
    alive := g.alive ++ ids,
    edges := g.edges ++ ids.flatMap (fun pid => (g.rowNeighbors d pid).map (fun w => (pid, w))),
    current_step := g.current_step + 1,
    map_parent := some d,
    dirty := g.dirty || g.skipsWindow d forb }

/-- Julia `do_up!`: la fila y, si una ventana se saltó, el review. -/
def up (g : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : GPathB :=
  if g.isValid then review (g.addNode d title forb) else g

/-- Julia `do_up_filtering!`. -/
def upFiltering (g : GPathB) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) : GPathB :=
  up (g.filterAll reqs) d title forb

/-- Julia `init_gpath_seed!`. -/
def initSeed (d : NodeId) (title : String) : GPathB :=
  up empty d title (fun _ => false)

-- ============================================================
-- El join (Julia do_join! + PathOwnersGraph.union!)
-- ============================================================

def mergeNode (a b : PNodeB) : PNodeB :=
  { a with
    parents := a.parents ++ b.parents.filter (fun p => !a.parents.contains p),
    sons := a.sons ++ b.sons.filter (fun s => !a.sons.contains s) }

def okJoin (g₁ g₂ : GPathB) : Bool :=
  g₁.current_step == g₂.current_step && g₁.map_parent == g₂.map_parent && g₁.isValid && g₂.isValid

/-- Unión: nodos con el mismo id se funden campo a campo; vivos y aristas se unen. -/
def join (g₁ g₂ : GPathB) : GPathB :=
  let nodes := g₁.nodes.map (fun n =>
    match g₂.node? n.id with
    | some m => mergeNode n m
    | none => n)
  { g₁ with
    nodes := nodes ++ g₂.nodes.filter (fun m => (g₁.node? m.id).isNone),
    alive := g₁.alive ++ g₂.alive.filter (fun q => !g₁.alive.contains q),
    edges := g₁.edges ++ g₂.edges.filter (fun e => !g₁.hasEdge e.1 e.2) }

def doJoin (g₁ g₂ : GPathB) : GPathB :=
  if okJoin g₁ g₂ then join g₁ g₂ else g₁

end GPathB

end AbsSatBingo.Model
