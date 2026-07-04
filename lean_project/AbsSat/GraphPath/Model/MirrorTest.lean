-- lean_project/AbsSat/GraphPath/Model/MirrorTest.lean
import AbsSat.GraphPath.Model.GPathM
import AbsSat.GraphMap.GraphMap
import Std.Data.HashSet

/-!
Phase F6 of `docs/plans/espejo_gpathm_lema_L1.md`: drive the whole SatMachine
loop *on the pure mirror* `GPathM`, plus a mirror exponential reader, so the
differential harness can compare three bands — oracle, IO executable, pure
mirror — on the same instances.

This module is validation infrastructure, not proof material: `partial def`
is acceptable here (nothing below is ever unfolded in a proof), and it may
consume the same loaded `GMap` the executable uses, since `GMap.get_node` /
`get_ids_step` are pure.
-/

namespace AbsSat.GraphPath.Model.MirrorTest

open AbsSat.Utils.Alias
open AbsSat.GraphMap.GraphMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- Pure machine loop over GPathM (mirror of SatMachine.run!)
-- ============================================================

/-- Timeline step: gpaths keyed by the map node just visited, exactly like
`ColTimelineStep` keys by `map_parent_id`. Collisions join. -/
abbrev MirrorLine := List (NodeId × GPathM)

def insertGPath (line : MirrorLine) (key : NodeId) (g : GPathM) : MirrorLine :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) =>
    line.map (fun kv => if kv.1 == key then (key, doJoin existing g) else kv)
  | none => line ++ [(key, g)]

/-- One machine step: every gpath is sent to every son of its origin node,
filtered by the destination's requirements (`send_to_destine_by_origin!`). -/
def mirrorAdvance (gmap : GMap) (line : MirrorLine) : MirrorLine :=
  line.foldl (fun next (kv : NodeId × GPathM) =>
    let (origin, g) := kv
    match get_node gmap origin with
    | none => next
    | some map_node =>
      map_node.sons.toList.foldl (fun next destine =>
        match get_node gmap destine with
        | none => next
        | some destine_node =>
          let g' := upFiltering g destine_node.requires.toList destine destine_node.title
          if isValid g' then insertGPath next destine g' else next)
        next)
    []

def mirrorInit (gmap : GMap) : MirrorLine :=
  (get_ids_step gmap 0).toList.foldl (fun line id =>
    match get_node gmap id with
    | none => line
    | some map_node => insertGPath line id (initSeed id map_node.title))
    []

def mirrorSteps (gmap : GMap) : Nat → MirrorLine → MirrorLine
  | 0, line => line
  | n + 1, line => mirrorSteps gmap n (mirrorAdvance gmap line)

/-- Run the mirror machine to the final map step. An empty result is UNSAT. -/
def mirrorRun (gmap : GMap) : MirrorLine :=
  mirrorSteps gmap (gmap.step - 1).toNat (mirrorInit gmap)

-- ============================================================
-- Mirror exponential reader (pure analogue of GPathExpReader)
-- ============================================================

private def dedupIds (ids : List NodeId) : List NodeId :=
  ids.foldl (fun acc id => if acc.contains id then acc else acc ++ [id]) []

/-- Enumerate every configuration represented by `g`: at each even step fork
per distinct surviving map node, filter by it, and advance two steps until the
clause block / fusion node is reached. A fork that invalidates the graph or
finds an empty step is an Owners-invariant violation and aborts with an
error, mirroring the Julia reader's `GRAVE ERROR`. -/
partial def readWork (work : List (GPathM × Array Bool × Int))
    (acc : List (Array Bool)) : Except String (List (Array Bool)) :=
  match work with
  | [] => .ok acc
  | (g, sol, k) :: rest =>
    let nodes_here := g.line k
    let candidates := dedupIds (nodes_here.map (·.id.id))
    if candidates.isEmpty then
      .error s!"mirror reader: no nodes at step {k}"
    else
      let forked : Except String (List (GPathM × Array Bool × Int) × List (Array Bool)) :=
        candidates.foldl (fun st mid => do
          let (work_acc, sols_acc) ← st
          let title :=
            match nodes_here.find? (fun n => n.id.id == mid) with
            | some n => n.title
            | none => ""
          if title.startsWith "or" || title.startsWith "Fusion" then
            pure (work_acc, sol :: sols_acc)
          else
            let g' := filterAll g [mid]
            if isValid g' then
              pure ((g', sol.push (mid.index == 1), k + 2) :: work_acc, sols_acc)
            else
              throw s!"mirror reader: graph invalidated selecting {mid} at step {k}")
          (.ok ([], []))
      match forked with
      | .error e => .error e
      | .ok (new_work, new_sols) => readWork (new_work ++ rest) (new_sols ++ acc)

def readAllMirror (g : GPathM) : Except String (List (Array Bool)) :=
  readWork [(g, #[], 0)] []

/-- Full mirror band for the differential harness: run the machine, read every
final gpath, return the union of solutions (empty = UNSAT). -/
def mirrorSolutions (gmap : GMap) : Except String (List (Array Bool)) := do
  let final := mirrorRun gmap
  let mut all : List (Array Bool) := []
  for (_, g) in final do
    let sols ← readAllMirror g
    all := sols ++ all
  pure all

end AbsSat.GraphPath.Model.MirrorTest
