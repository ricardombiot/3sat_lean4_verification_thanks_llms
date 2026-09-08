-- lean_project/AbsSat/GraphPath/Model/WidthProbe.lean
import AbsSat.GraphPath.Model.MirrorTest
import AbsSat.GraphMap.ImportCnf

/-!
Measures the two quantities the complexity claim rests on, on a real CNF:

* **gpaths per step** — the timeline keys gpaths by destination map node and
  joins collisions, so this is bounded by the map nodes at a step (≤ 7, the
  clause block).
* **path-nodes per layer** — a `PathNodeId` is `(id, parent_id)`, one level of
  history only. So a layer holds at most (map nodes at `k`) × (map nodes at
  `k-1`, plus `none`) ≤ 7 × 8 = **56**, independent of the formula size.

Neither bound involves `n` or `m`. Run with `lake exe width <file.cnf>`.
-/

namespace AbsSat.GraphPath.Model.WidthProbe

open AbsSat.Utils.Alias AbsSat.GraphMap.GraphMap AbsSat.GraphMap.ImportCnf
open AbsSat.GraphPath.Model.GPathM AbsSat.GraphPath.Model.MirrorTest

/-- Map size: `(steps, nodes)`. The construction gives `2n + m + 2` steps and
`4n + 7m + 2` nodes — linear in the formula. -/
def mapSize (gmap : GMap) : Nat × Nat :=
  let steps := (List.range (GMap.step gmap).toNat).map (fun i : Nat => (i : Int))
  (steps.length, steps.foldl (fun acc s => acc + (get_ids_step gmap s).size) 0)

partial def walk (gmap : GMap) (line : MirrorLine) (fuel : Nat)
    (accW accL accN : Nat) : Nat × Nat × Nat :=
  if fuel = 0 || line.isEmpty then (accW, accL, accN) else
    let w := line.length
    let maxLine := line.foldl (fun a kv =>
      Nat.max a ((intRange 0 (kv.2.current_step - 1)).foldl
        (fun b j => Nat.max b (kv.2.line j).length) 0)) 0
    let maxNodes := line.foldl (fun a kv => Nat.max a kv.2.nodes.length) 0
    walk gmap (mirrorAdvance gmap line) (fuel - 1)
      (Nat.max accW w) (Nat.max accL maxLine) (Nat.max accN maxNodes)

def report (path : String) : IO Unit := do
  let gmap ← load_import! path
  let (steps, nodes) := mapSize gmap
  let vars := gmap.literals_counter / 2
  let clauses := gmap.clausule_counter
  IO.println s!"{path}"
  IO.println s!"  formula      vars={vars} clauses={clauses}"
  IO.println s!"  map          steps={steps} (2n+m+2={2*vars+clauses+2})  \
nodes={nodes} (4n+7m+2={4*vars+7*clauses+2})"
  let (w, l, n) := walk gmap (mirrorInit gmap) 1000 0 0 0
  IO.println s!"  machine      max gpaths/step={w}  max path-nodes/layer={l} (bound 56)  \
max nodes/gpath={n}"

end AbsSat.GraphPath.Model.WidthProbe
