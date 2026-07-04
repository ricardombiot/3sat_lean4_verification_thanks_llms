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

/--
Mark `step` invalid (and record it in `emptySteps`) if its owners set has become empty.
Mirrors Julia's `check_if_isempty!`, which is what lets a broken step actually
invalidate the graph.
-/
def checkIfEmpty (owners : PathDocOwners) (step : Int) : PathDocOwners :=
  match owners.table.get? step with
  | some s =>
    if s.isEmpty then
      { owners with emptySteps := owners.emptySteps.insert step, valid := false }
    else
      owners
  | none => owners

def remove (owners : PathDocOwners) (id : PathNodeId) : PathDocOwners :=
  let step := id.id.step
  match owners.table.get? step with
  | some s =>
    let set := s.erase id
    -- Keep the (possibly empty) key, matching Julia: emptiness is detected by
    -- checkIfEmpty below, not by erasing the table entry.
    let owners := { owners with table := owners.table.insert step set }
    checkIfEmpty owners step
  | none => owners

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

/--
Intersect the owners set of `a` at a single `step` with `b`'s set at that same
step (only when both have an entry there), then check whether that emptied it.
-/
def intersectStep (owners : PathDocOwners) (b : PathDocOwners) (step : Int) : PathDocOwners :=
  match owners.table.get? step, b.table.get? step with
  | some setA, some setB =>
    let newSet : Std.HashSet PathNodeId :=
      setA.fold (fun s item => if setB.contains item then s.insert item else s) {}
    let owners := { owners with table := owners.table.insert step newSet }
    checkIfEmpty owners step
  | _, _ => owners

partial def intersectFrom (owners : PathDocOwners) (b : PathDocOwners) (step : Int) : PathDocOwners :=
  if step > owners.maxStep then
    owners
  else
    intersectFrom (intersectStep owners b step) b (step + 1)

/--
Intersect `a` with `b`, in place semantics mirrored from Julia's `intersect!`:
only `a` is updated. If `b` reaches further than `a` ever did, `a` is
immediately invalid (it cannot possibly agree with owners at steps it never
recorded). Otherwise every step `a` knows about gets intersected against `b`,
and `checkIfEmpty` marks the graph invalid the moment any step is left without
an owner.
-/
def intersect (a b : PathDocOwners) : PathDocOwners :=
  if b.maxStep > a.maxStep then
    { a with valid := false }
  else
    intersectFrom a b 0


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
