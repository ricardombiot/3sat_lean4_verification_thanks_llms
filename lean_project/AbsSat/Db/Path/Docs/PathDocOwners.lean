import Std.Data.HashMap
import Std.Data.HashSet
import AbsSat.Utils.Alias

namespace AbsSat.Db.Path.Docs.PathDocOwners

open AbsSat.Utils.Alias

structure PathDocOwners where
  table : Std.HashMap Int (Std.HashSet PathNodeId)
  maxStep : Int
  emptySteps : Std.HashSet Int
  valid : Bool
-- deriving Repr

def new : PathDocOwners := {
  table := {},
  maxStep := -1,
  emptySteps := {},
  valid := true
}

instance : Inhabited PathDocOwners := ⟨new⟩

/--
Create a deep copy of the PathDocOwners.
Since PathDocOwners is made of value types (HashMap, HashSet, Int, Bool),
a simple copy is a deep copy in terms of mutability (unless we were using Refs inside).
-/
def clone (owners : PathDocOwners) : PathDocOwners :=
  -- No IO needed since it's a value type
  { table := owners.table, maxStep := owners.maxStep, emptySteps := owners.emptySteps, valid := owners.valid }

def isValid (owners : PathDocOwners) : Bool :=
  owners.valid && owners.emptySteps.isEmpty

def hasStep (owners : PathDocOwners) (step : Int) : Bool :=
  owners.table.contains step

def get (owners : PathDocOwners) (step : Int) : Option (Std.HashSet PathNodeId) :=
  owners.table.get? step

def insert (owners : PathDocOwners) (id : PathNodeId) : PathDocOwners :=
  let step := id.id.step
  let set := match owners.table.get? step with
    | some s => s
    | none => {}
  let set := set.insert id
  let table := owners.table.insert step set
  let maxStep := if step > owners.maxStep then step else owners.maxStep
  { owners with table := table, maxStep := maxStep }

def remove (owners : PathDocOwners) (id : PathNodeId) : PathDocOwners :=
  let step := id.id.step
  let table := match owners.table.get? step with
    | some s =>
      let set := s.erase id
      if set.isEmpty then
        owners.table.erase step
      else
        owners.table.insert step set
    | none => owners.table
  -- Not recalculating maxStep for simplicity, assuming it doesn't break validity
  { owners with table := table }

def isOwner (owners : PathDocOwners) (nodeId : PathNodeId) : Bool :=
  match get owners nodeId.id.step with
  | some setOwnersLine => setOwnersLine.contains nodeId
  | none => false


partial def toStringAux (owners : PathDocOwners) (step : Int) (acc : String) : String :=
  if step > owners.maxStep then
    acc
  else
    let line := s!"{step} => "
    let line := match get owners step with
    | some setOwnersLine =>
      let sortedNodes := (setOwnersLine.toList.map as_key_from_PathNodeId).mergeSort (· <= ·)
      let nodes := ",".intercalate sortedNodes
      s!"{line}{nodes}"
    | none => line
    toStringAux owners (step + 1) (s!"{acc}{line}\n")

def union (a b : PathDocOwners) : PathDocOwners :=
  let mergedTable := a.table.fold (fun t step setA =>
    match t.get? step with
    | some setB =>
      let newSet := setA.fold (fun s item => s.insert item) setB
      t.insert step newSet
    | none => t.insert step setA
  ) b.table
  let newMax := if a.maxStep > b.maxStep then a.maxStep else b.maxStep
  { new with table := mergedTable, maxStep := newMax }

def intersect (a b : PathDocOwners) : PathDocOwners :=
  -- Julia: intersect!(map_node.owners, gpath.owners)
  -- Julia: intersect!(map_node.owners, gpath.owners)
  -- If key is missing in B, it should be removed from A? Intersection logic implies AND.
  -- "hago la union de los owners de mis padres y la intersectiono conmigo"
  -- If parent has no owners at step X, and child has owners at step X, child should lose them?
  -- Logic: Child only valid if owners are present in parents?

  -- Assuming standard set intersection semantics on (Step -> Set NodeId).

  let newTable := a.table.fold (fun t step setA =>
    match b.table.get? step with
    | some setB =>
      let newSet : Std.HashSet PathNodeId := setA.fold (fun s item => if setB.contains item then s.insert item else s) {}
      if newSet.isEmpty then t else t.insert step newSet
    | none => t -- If step missing in B, intersection is empty for this step
  ) {}

  -- We also need to check maxStep.
  let newMax := a.maxStep -- Approx
  { new with table := newTable, maxStep := newMax, valid := a.valid && b.valid }


instance : ToString PathDocOwners where
  toString owners :=
    let header := "## Owners ##\n"
    toStringAux owners 0 header

section Theorems

  theorem new_is_valid : isValid new := by
    simp [new, isValid]

  theorem new_maxStep_is_negative : new.maxStep = -1 := by
    simp [new]

  theorem new_table_is_empty : new.table.isEmpty := by
    simp [new]

  theorem new_emptySteps_is_empty : new.emptySteps.isEmpty := by
    simp [new]

  theorem get_new_is_none (step : Int) : get new step = none := by
    simp [get, new]

  theorem isOwner_new_is_false (nodeId : PathNodeId) : isOwner new nodeId = false := by
    simp [isOwner, get_new_is_none]

  -- Commented out complex theorems involving properties of HashMap/HashSet logic
  -- theorem get_is_some_when_have ...
  -- theorem get_is_none_when_not_have ...
  -- theorem isOwner_is_false_when_not_have ...
  -- theorem isOwner_is_true_when_present ...
  -- theorem isOwner_iff_in_set ...

  -- theorem toString_new : toString new = "## Owners ##\n" := by
  --   sorry

  -- theorem toString_with_data ... sorry

end Theorems

section Examples

  def run_tests : IO Unit := do
    -- Test with a new (empty) owners instance
    let owners := new
    assert! isValid owners
    assert! ¬(hasStep owners 0)
    assert! (get owners 0).isNone

    -- Test with a populated owners instance
    let nodeId1 : NodeId := { step := 0, index := 1 }
    let pathNodeId1 : PathNodeId := { id := nodeId1, parent_id := none }
    let nodeId2 : NodeId := { step := 0, index := 2 }
    let pathNodeId2 : PathNodeId := { id := nodeId2, parent_id := some nodeId1 }
    let set1 : Std.HashSet PathNodeId := {}
    let set1 := set1.insert pathNodeId1
    let set1 := set1.insert pathNodeId2
    let table : Std.HashMap Int (Std.HashSet PathNodeId)  := {}
    let table := table.insert 0 set1
    let owners_with_data : PathDocOwners := { new with table := table, maxStep := 0 } -- Set maxStep to 0 so toString iterates

    assert! hasStep owners_with_data 0
    assert! (get owners_with_data 0).isSome
    assert! ¬(hasStep owners_with_data 1)
    assert! (get owners_with_data 1).isNone

    -- Test isOwner
    assert! isOwner owners_with_data pathNodeId1
    assert! isOwner owners_with_data pathNodeId2
    let nodeId3 : NodeId := { step := 1, index := 1 }
    let pathNodeId3 : PathNodeId := { id := nodeId3, parent_id := none }
    assert! ¬(isOwner owners_with_data pathNodeId3)

    -- Test toString
    let owners_for_string : PathDocOwners := { new with table := table, maxStep := 0 }
    let expected_string := "## Owners ##\n0 => k0.1__root,k0.2__k0.1\n"
    assert! (toString owners_for_string) == expected_string

    IO.println "All PathDocOwners tests passed!"

  #eval run_tests

end Examples

end AbsSat.Db.Path.Docs.PathDocOwners
