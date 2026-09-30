-- lean/improves_bingo/AbsSatBingo/Exe/Dump.lean
import AbsSatBingo.Model.ForbidOn

/-!
# Volcado canónico del estado final (fase L3)

El mismo formato que `julia/improves_bingo/test_3sat/dump_final.jl`, para comparar con `compare_bingo.jl`
(modo `states`): por cada gpath de la línea final, ordenados por su nodo de mapa, sus nodos, sus vivos y, por nodo,
su tabla de owners (los vivos que posee, él incluido), sus padres y sus hijos; todo como claves de Julia
(`as_key`) ordenadas. Las soluciones no se vuelcan: el lector de Lean no es el exponencial de Julia.
-/

namespace AbsSatBingo.Exe.Dump

open AbsSatBin.Utils.Alias
open AbsSatBingo.Model
open AbsSatBingo.Model.GPathB

def keyOf (q : PathNodeId) : String := as_key_from_PathNodeId q

def keysSorted (l : List PathNodeId) : String :=
  String.intercalate "," ((l.map keyOf).eraseDups.toArray.qsort (· < ·)).toList

/-- La tabla de owners de `x`: los vivos que posee (él incluido si vive). -/
def ownersOf (g : GPathB) (x : PathNodeId) : List PathNodeId :=
  g.alive.filter (g.adjb x)

def dumpGPath (g : GPathB) : String :=
  let nodes := (g.nodes.toArray.qsort (fun a b => keyOf a.id < keyOf b.id)).toList
  let mp := match g.map_parent with | some d => as_key d | none => "nothing"
  let head := s!"gpath {mp} step={g.current_step} valid={g.isValid}\n" ++
    s!"  nodes {keysSorted (nodes.map (·.id))}\n" ++
    s!"  global {keysSorted g.alive}\n"
  nodes.foldl (fun acc n =>
    acc ++ s!"  node {keyOf n.id}\n" ++
      s!"    owners {keysSorted (ownersOf g n.id)}\n" ++
      s!"    parents {keysSorted n.parents}\n" ++
      s!"    sons {keysSorted n.sons}\n") head

/-- Los tríos por arista (Julia `forbid <a>|<b> r1,…`): los `r` con `{a, b, r}` escrito, para cada arista. -/
def dumpForbid (g : GPathB) : String :=
  let cand := (g.trios.flatMap (fun t => [t.1, t.2.1, t.2.2])).eraseDups
  let lines := g.edges.filterMap (fun e =>
    let rs := cand.filter (fun r => g.trios.any (trioIs e.1 e.2 r))
    if rs.isEmpty then none
    else
      let ab := ([keyOf e.1, keyOf e.2].toArray.qsort (· < ·)).toList
      some s!"  forbid {ab.getD 0 ""}|{ab.getD 1 ""} {keysSorted rs}\n")
  String.join (lines.toArray.qsort (· < ·)).toList

/-- El volcado para el diferencial del modo FORBID (Julia `dump_forbid.jl`): sin soluciones, con los tríos. -/
def dumpForbidRun (name : String) (sat : Bool) (line : Driver.Line) : String :=
  let gs := (line.map (·.2)).toArray.qsort (fun a b =>
    (match a.map_parent with | some d => as_key d | none => "") <
    (match b.map_parent with | some d => as_key d | none => ""))
  s!"instance {name}\nsat {sat}\n" ++ String.join (gs.toList.map (fun g => dumpGPath g ++ dumpForbid g))

/-- El fichero de una instancia. -/
def dumpRun (name : String) (truth sat : Bool) (line : Driver.Line) : String :=
  let gs := (line.map (·.2)).toArray.qsort (fun a b =>
    (match a.map_parent with | some d => as_key d | none => "") <
    (match b.map_parent with | some d => as_key d | none => ""))
  s!"instance {name}\ntruth {truth} sat {sat}\nsolutions -\n" ++
    String.join (gs.toList.map dumpGPath)

end AbsSatBingo.Exe.Dump
