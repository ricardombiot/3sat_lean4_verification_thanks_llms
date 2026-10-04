-- lean/improves_bingo/AbsSatBingo/Tagged/Defs.lean
import AbsSatBingo.Model.Driver

/-!
# La máquina con etiquetas por fila (fase T1 de `docs/plans/lean_row_tags.md`)

Espejo de `julia/improves_bingo` con `ROW_TAGS=on` (informe v205): `path_owners_graph.jl` (etiquetas),
`graph_path_tags.jl` (la regla) y los enganches en `do_up_filtering!`, `create_from_parents!`, `union!` y
`make_review_owners!`.

Una capa aparte sobre `GPathB`, que no se toca: `TGPath` es el gpath más sus etiquetas. Una etiqueta `(x, w, ℓ, a)`
dice que el par `x–w` (en cualquier orientación; reflexivo para un nodo) viene de la pieza de la clave `a` en la
fila de claves `ℓ`. Como `GPathB`, es un modelo de especificación: listas, y cada poda un `filter`.

Diferencias con Julia, a propósito:
* Julia guarda una máscara de bits por fila; aquí, la lista de etiquetas (puede tener repetidas).
* Julia solo mira las filas mezcladas; aquí, todas. En una fila con una sola clave, todo par vivo la lleva, y en el
  punto fijo del review de siempre la regla no quita nada (a demostrar en T3).
* Las etiquetas de pares muertos pueden quedar en la lista; la regla las quita en su siguiente pasada, y ninguna
  consulta las ve, porque `padj` pide la posesión viva.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

/-- Una etiqueta: el par, la fila de claves y la clave. -/
abbrev TagE := PathNodeId × PathNodeId × Int × NodeId

/-- El gpath con sus etiquetas. `krows`: las filas de claves marcadas (las filas `0 … krows-1`). -/
structure TGPath where
  g     : GPathB
  tags  : List TagE
  krows : Int

namespace TGPath

open GPathB

-- ============================================================
-- Consultas
-- ============================================================

/-- La etiqueta `e` es del par `x–w`, en la fila `ℓ`. -/
def tagOn (x w : PathNodeId) (ℓ : Int) (e : TagE) : Bool :=
  ((e.1 == x && e.2.1 == w) || (e.1 == w && e.2.1 == x)) && e.2.2.1 == ℓ

def hasTag (T : List TagE) (x w : PathNodeId) (ℓ : Int) (a : NodeId) : Bool :=
  T.any (fun e => tagOn x w ℓ e && e.2.2.2 == a)

/-- El par tiene alguna clave en la fila `ℓ`. -/
def hasRow (T : List TagE) (x w : PathNodeId) (ℓ : Int) : Bool :=
  T.any (tagOn x w ℓ)

/-- **La posesión dentro de la pieza** `(ℓ, a)`: se poseen y el par lleva `a` en `ℓ` (Julia `tag_sub`). -/
def padj (g : GPathB) (T : List TagE) (ℓ : Int) (a : NodeId) (x w : PathNodeId) : Bool :=
  g.adjb x w && hasTag T x w ℓ a

-- ============================================================
-- Dónde se escriben (Julia stamp!, create_from_parents!, union!)
-- ============================================================

/-- Añade a `T` las etiquetas de `U` que aún no tiene (Julia: el OR de las máscaras). Sin esto las listas crecen con
repetidas en cada join, porque las llegadas comparten la historia del remitente. -/
def tagUnion (T U : List TagE) : List TagE :=
  U.foldl (fun acc e => if acc.contains e then acc else acc ++ [e]) T

/-- **La llegada** (Julia `stamp!`): todo lo vivo de la copia del remitente viene de la pieza de su clave `k`, en la
fila de su cima `k.step`. -/
def stamp (tg : TGPath) (k : NodeId) : TGPath :=
  { tg with
    tags := tagUnion tg.tags
      (tg.g.alive.map (fun x => (x, x, k.step, k)) ++ tg.g.edges.map (fun e => (e.1, e.2, k.step, k))),
    krows := tg.krows + 1 }

/-- Las etiquetas que hereda la fila nueva (Julia `create_from_parents!`): el nodo nuevo, las de sus padres vivos; la
arista `pid–w`, las de las aristas vivas `p–w` de sus padres (con `w = p` si es la reflexiva del padre). -/
def inheritTags (g : GPathB) (T : List TagE) (d : NodeId) (forb : PathNodeId → Bool) : List TagE :=
  (g.newRowIds d forb).flatMap (fun pid =>
    let ps := g.rowParents d pid
    let ws := g.rowNeighbors d pid
    T.flatMap (fun e =>
      let x := e.1; let w := e.2.1; let ℓ := e.2.2.1; let a := e.2.2.2
      (if x == w && ps.contains x && g.isAlive x then [(pid, pid, ℓ, a), (pid, x, ℓ, a)] else []) ++
      (if x != w && ps.contains x && ws.contains w && g.adjb x w then [(pid, w, ℓ, a)] else []) ++
      (if x != w && ps.contains w && ws.contains x && g.adjb x w then [(pid, x, ℓ, a)] else [])))

/-- La fila nueva, con sus etiquetas. -/
def addNodeT (tg : TGPath) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : TGPath :=
  { g := tg.g.addNode d title forb, tags := tagUnion tg.tags (inheritTags tg.g tg.tags d forb), krows := tg.krows }

/-- El join: las etiquetas se unen (Julia, OR fila a fila). -/
def doJoinT (a b : TGPath) : TGPath :=
  if okJoin a.g b.g then { g := join a.g b.g, tags := tagUnion a.tags b.tags, krows := a.krows } else a

-- ============================================================
-- La regla de la etiqueta (Julia graph_path_tags.jl)
-- ============================================================

/-- Un enlace de `u` (padre o hijo) dentro de la pieza que llega a `v` dentro de la pieza. -/
def linkIn (g : GPathB) (T : List TagE) (ℓ : Int) (a : NodeId) (links : List PathNodeId) (u v : PathNodeId) : Bool :=
  links.any (fun p => padj g T ℓ a u p && padj g T ℓ a p v)

/-- Los apoyos de `u` hacia `v` dentro de la pieza: un padre (si no es raíz) y un hijo (si no es cima). -/
def supportIn (g : GPathB) (T : List TagE) (ℓ : Int) (a : NodeId) (u v : PathNodeId) : Bool :=
  match g.node? u with
  | none => false
  | some n =>
    (u.parent_id.isNone || linkIn g T ℓ a n.parents u v) &&
    (u.id.step == g.current_step - 1 || linkIn g T ℓ a n.sons u v)

/-- **Nodo** (Julia `tag_node_keeps`): un vecino de la pieza en cada paso, y sus enlaces dentro de la pieza. -/
def nodeKeeps (g : GPathB) (T : List TagE) (ℓ : Int) (a : NodeId) (x : PathNodeId) : Bool :=
  padj g T ℓ a x x &&
  (intRange 0 (g.current_step - 1)).all (fun k => g.alive.any (fun r => r.id.step == k && padj g T ℓ a x r)) &&
  supportIn g T ℓ a x x

/-- **Arista** (Julia `tag_edge_keeps`): los dos extremos y la arista en la pieza; un testigo común de la pieza en
cada paso (regla de parejas); y los apoyos de cada extremo hacia el otro (pasadas de padres e hijos). -/
def edgeKeeps (g : GPathB) (T : List TagE) (ℓ : Int) (a : NodeId) (x w : PathNodeId) : Bool :=
  padj g T ℓ a x x && padj g T ℓ a w w && padj g T ℓ a x w &&
  (intRange 0 (g.current_step - 1)).all (fun k =>
    g.alive.any (fun r => r.id.step == k && padj g T ℓ a x r && padj g T ℓ a w r)) &&
  supportIn g T ℓ a x w && supportIn g T ℓ a w x

/-- Una etiqueta se queda si su par la sigue mereciendo en su pieza. -/
def tagKeeps (g : GPathB) (T : List TagE) (e : TagE) : Bool :=
  if e.1 == e.2.1 then nodeKeeps g T e.2.2.1 e.2.2.2 e.1 else edgeKeeps g T e.2.2.1 e.2.2.2 e.1 e.2.1

/-- Una pasada de la regla, en dos fases: todas las etiquetas se deciden contra el estado de antes. -/
def tagSweep (g : GPathB) (T : List TagE) : List TagE :=
  T.filter (tagKeeps g T)

/-- Lo que se queda sin clave en alguna fila muere: los nodos salen del grafo (`killVertex`, como el filtro por
requisito; la purga los retira después) y las aristas se quitan. -/
def tagCut (g : GPathB) (T : List TagE) (krows : Int) : GPathB :=
  let rows := intRange 0 (krows - 1)
  let dead := g.alive.filter (fun x => !rows.all (hasRow T x x))
  let g' := dead.foldl killVertex g
  { g' with edges := g'.edges.filter (fun e => rows.all (hasRow T e.1 e.2)) }

-- ============================================================
-- El review con la regla (Julia make_review_owners!)
-- ============================================================

/-- Julia `make_review_owners!` con `ROW_TAGS=on`: solo con `dirty`; el review de siempre hasta su punto fijo, y
entonces la regla; si quita alguna etiqueta, otra vuelta. -/
def reviewTFuel : Nat → TGPath → TGPath
  | 0, tg => tg
  | n + 1, tg =>
    if tg.g.isValid && tg.g.dirty then
      let g₁ := review tg.g
      if g₁.isValid then
        let T' := tagSweep g₁ tg.tags
        if T'.length < tg.tags.length then
          reviewTFuel n { g := { tagCut g₁ T' tg.krows with dirty := true }, tags := T', krows := tg.krows }
        else { tg with g := g₁ }
      else { tg with g := g₁ }
    else tg

/-- Cada vuelta que sigue quita alguna etiqueta: `tags.length + 1` vueltas bastan. -/
def reviewT (tg : TGPath) : TGPath :=
  reviewTFuel (tg.tags.length + 1) tg

/-- Julia `filter!`. -/
def filterAllT (tg : TGPath) (reqs : List NodeId) : TGPath :=
  reviewT { tg with g := reqs.foldl filterRequire tg.g }

/-- Julia `do_up!`. -/
def upT (tg : TGPath) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : TGPath :=
  if tg.g.isValid then reviewT (tg.addNodeT d title forb) else tg

/-- Julia `do_up_filtering!`: primero la marca de la llegada, después el filtro y la fila. -/
def upFilteringT (tg : TGPath) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) : TGPath :=
  let tg := match tg.g.map_parent with
    | some k => tg.stamp k
    | none => tg
  upT (tg.filterAllT reqs) d title forb

def initSeedT (d : NodeId) (title : String) : TGPath :=
  upT { g := GPathB.empty, tags := [], krows := 0 } d title (fun _ => false)

end TGPath

-- ============================================================
-- La máquina y el lector con etiquetas (espejo de Driver)
-- ============================================================

namespace DriverT

open TGPath

abbrev LineT := List (NodeId × TGPath)

def insertT (line : LineT) (key : NodeId) (tg : TGPath) : LineT :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) => line.map (fun kv => if kv.1 == key then (key, doJoinT existing tg) else kv)
  | none => line ++ [(key, tg)]

def sendToT (φ : Cnf) (tg : TGPath) (next : LineT) (d : NodeId) : LineT :=
  let tg' := tg.upFilteringT (reqOf φ d) d "" (isProhibited φ)
  if tg'.g.isValid then insertT next d tg' else next

def sendAllT (φ : Cnf) (kv : NodeId × TGPath) (next : LineT) : LineT :=
  (sonsOfMap φ kv.1).foldl (sendToT φ kv.2) next

def advanceT (φ : Cnf) (line : LineT) : LineT :=
  line.foldl (fun next kv => sendAllT φ kv next) []

def initT (φ : Cnf) : LineT :=
  (mapNodes φ 0).foldl (fun line id => insertT line id (initSeedT id "")) []

def stepsT (φ : Cnf) : Nat → LineT → LineT
  | 0, line => line
  | n + 1, line => stepsT φ n (advanceT φ line)

/-- **La máquina con etiquetas.** -/
def runT (φ : Cnf) : LineT := stepsT φ (stepCount φ - 1).toNat (initT φ)

def machineVerdictT (φ : Cnf) : Bool := !(runT φ).isEmpty

/-- Fija el primer nodo del paso `k` que el review etiquetado deja válido. -/
def tryPinsT (tg : TGPath) (k : Int) : Option TGPath :=
  (tg.g.alive.filter (fun q => q.id.step == k)).findSome? (fun q =>
    let h := tg.filterAllT [q.id]
    if h.g.isValid then some h else none)

def readLoopT : Nat → TGPath → Option TGPath
  | 0, tg => if Driver.hasChoice tg.g then none else some tg
  | n + 1, tg =>
    match Driver.firstChoice tg.g with
    | none => some tg
    | some k =>
      match tryPinsT tg k with
      | none => none
      | some h => readLoopT n h

def reviewAllT (tg : TGPath) : TGPath := reviewT { tg with g := { tg.g with dirty := true } }

def readGT (tg : TGPath) : Option TGPath :=
  let tg := reviewAllT tg
  if tg.g.isValid then readLoopT tg.g.measure tg else none

/-- **El veredicto del lector con etiquetas.** -/
def readerVerdictT (φ : Cnf) : Bool :=
  (runT φ).any (fun kv => (readGT kv.2).isSome)

end DriverT

end AbsSatBingo.Model
