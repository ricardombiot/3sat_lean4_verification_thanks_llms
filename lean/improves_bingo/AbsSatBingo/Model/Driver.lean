-- lean/improves_bingo/AbsSatBingo/Model/Driver.lean
import AbsSatBingo.Model.Ops
import AbsSatBin.GraphMap.CnfMapBin

/-!
# La máquina y el lector sobre `GPathB`

Fase L2 de `docs/plans/lean_bingo.md`.

* **La máquina** es la de `lean/improves_bin` (`PureDriver`) sobre el mapa bin aritmético (`CnfMapBin`): cada
  estado va a cada hijo de su nodo de mapa, filtrado por los requisitos del destino, y los estados que llegan al
  mismo nodo se unen (Julia `sat_machine.jl` + `CollectionTimelineStep.impact!`). Los títulos van vacíos: nada los
  lee y el volcado no los escribe.
* **El lector** es el de `ReaderExec` (sin retroceso): en cada vuelta toma el primer paso con elección, fija el
  primer nodo que el review deja válido y sigue. El estado de partida se revisa entero (`reviewAll`): en bingo el
  review solo corre con `dirty`, y el estado de la línea final viene de un join, que no revisa.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace Driver

open GPathB

-- ============================================================
-- La máquina
-- ============================================================

/-- Una línea del timeline: estados por el nodo de mapa que acaban de visitar. -/
abbrev Line := List (NodeId × GPathB)

/-- Los estados que llegan al mismo nodo de mapa se unen. -/
def insert (line : Line) (key : NodeId) (g : GPathB) : Line :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) => line.map (fun kv => if kv.1 == key then (key, doJoin existing g) else kv)
  | none => line ++ [(key, g)]

/-- Un estado a un destino; solo se guarda si queda válido. -/
def sendTo (φ : Cnf) (g : GPathB) (next : Line) (d : NodeId) : Line :=
  let g' := g.upFiltering (reqOf φ d) d "" (isProhibited φ)
  if g'.isValid then insert next d g' else next

def sendAll (φ : Cnf) (kv : NodeId × GPathB) (next : Line) : Line :=
  (sonsOfMap φ kv.1).foldl (sendTo φ kv.2) next

def advance (φ : Cnf) (line : Line) : Line :=
  line.foldl (fun next kv => sendAll φ kv next) []

def init (φ : Cnf) : Line :=
  (mapNodes φ 0).foldl (fun line id => insert line id (initSeed id "")) []

def steps (φ : Cnf) : Nat → Line → Line
  | 0, line => line
  | n + 1, line => steps φ n (advance φ line)

/-- **La máquina entera.** Una línea final vacía es la respuesta UNSAT. -/
def run (φ : Cnf) : Line := steps φ (stepCount φ - 1).toNat (init φ)

def machineVerdict (φ : Cnf) : Bool := !(run φ).isEmpty

-- ============================================================
-- El lector (ReaderExec, sobre GPathB)
-- ============================================================

/-- En el paso `k` quedan vivos de dos nodos de mapa distintos. -/
def choiceAt (g : GPathB) (k : Int) : Bool :=
  let at_k := g.alive.filter (fun q => q.id.step == k)
  at_k.any (fun q => at_k.any (fun r => q.id != r.id))

def hasChoice (g : GPathB) : Bool :=
  (intRange 0 (g.current_step - 1)).any (choiceAt g)

def firstChoice (g : GPathB) : Option Int :=
  (intRange 0 (g.current_step - 1)).find? (choiceAt g)

/-- Fija el primer nodo del paso `k` que el review deja válido. -/
def tryPins (g : GPathB) (k : Int) : Option GPathB :=
  (g.alive.filter (fun q => q.id.step == k)).findSome? (fun q =>
    let h := g.filterAll [q.id]
    if h.isValid then some h else none)

/-- El bucle del lector: nunca deshace un pin. Cada pin quita algo, así que `measure` vueltas bastan. -/
def readLoop : Nat → GPathB → Option GPathB
  | 0, g => if hasChoice g then none else some g
  | n + 1, g =>
    match firstChoice g with
    | none => some g
    | some k =>
      match tryPins g k with
      | none => none
      | some h => readLoop n h

/-- El review entero sobre un estado (con `dirty` activado). -/
def reviewAll (g : GPathB) : GPathB := review { g with dirty := true }

def readG (g : GPathB) : Option GPathB :=
  let g := reviewAll g
  if g.isValid then readLoop g.measure g else none

/-- **El veredicto del lector**: SAT si termina sobre algún estado de la línea final. -/
def readerVerdict (φ : Cnf) : Bool :=
  (run φ).any (fun kv => (readG kv.2).isSome)

-- ============================================================
-- Fuerza bruta y nodos muertos
-- ============================================================

/-- El veredicto por fuerza bruta, para fórmulas pequeñas. -/
def bruteSat (φ : Cnf) : Bool :=
  (List.range (2 ^ φ.nVars)).any (fun m => satB (fun v => m.testBit v) φ)

/-- Ningún nodo por debajo de la cima sin hijos (Julia `GRAVE ERROR READER`). -/
def noDeadNodes (g : GPathB) : Bool :=
  g.nodes.all (fun n => n.id.id.step == g.current_step - 1 || !n.sons.isEmpty)

end Driver

end AbsSatBingo.Model
