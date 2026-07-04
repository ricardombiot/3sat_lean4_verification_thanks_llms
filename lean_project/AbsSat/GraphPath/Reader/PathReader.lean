-- lean_project/AbsSat/GraphPath/Reader/PathReader.lean
import AbsSat.GraphPath.GraphPath
import AbsSat.Utils.Alias
import Std.Data.HashSet

/-!
Port of `docs/original_julia/src/graph_path/reader/path_reader.jl`.

Reading a solution out of a filtered `GPath` is nothing but the machine's own
`filter!` applied with unit requirement sets: at each even step (the literal
value steps) select a surviving node, record its `index` (0/1) as the value of
that variable, then filter the graph by that selection and advance two steps.
Reading stops when the selected node belongs to the clause block (`or*`) or is
a `FusionNode` — the literal block is over and `solution` holds one bit per
variable, in variable order.

The Julia reader throws `"GRAVE ERROR READER... GPATH INVALID."` if a filter
ever invalidates the graph: the design invariant is that every surviving node
is extendable to a full solution. Here that situation is surfaced as
`error := some msg` instead of an exception, so harnesses can report it as a
finding (it is precisely an Owners-invariant violation).
-/

namespace AbsSat.GraphPath.Reader

open AbsSat.Utils.Alias
open AbsSat.GraphPath
open AbsSat.Db.Path.Cols.PathColLines

structure GPathReader where
  gpath : GPath
  solution : Array Bool
  step : Step
  is_finished : Bool
  error : Option String

def GPathReader.new (gpath : GPath) : GPathReader := {
  gpath := gpath,
  solution := #[],
  step := 0,
  is_finished := false,
  error := none
}

/--
A node title marks the end of the literal block when it belongs to the clause
block (`or{k}={case}`) or is a fusion node. Variable titles produced by
`ImportCnf` are numeric (`3=0`, `!3=1`), so prefix checks are unambiguous.
-/
def title_ends_literals (title : String) : Bool :=
  title.startsWith "or" || title.startsWith "Fusion"

/--
Register the selected node (append its bit to `solution` unless it closes the
literal block) and filter the reader's gpath by the selection — the read-side
mirror of Julia's `register_selection!` + `filter_gpath!`. Mutates the
reader's gpath in place; callers that need the graph intact must clone first.
-/
def register_and_filter! (reader : GPathReader) (selected : PathNodeId) : IO GPathReader := do
  let node? ← getNode reader.gpath.table_lines selected
  match node? with
  | none =>
    pure { reader with
      error := some s!"reader: selected node {selected} missing at step {reader.step}",
      is_finished := true }
  | some node =>
    if title_ends_literals node.title then
      pure { reader with is_finished := true }
    else
      let bit := node.id.id.index == 1
      let reader := { reader with solution := reader.solution.push bit }
      let requires : Std.HashSet NodeId := ({} : Std.HashSet NodeId).insert selected.id
      filter! reader.gpath requires
      let valid ← reader.gpath.is_valid.get
      if valid then
        pure { reader with step := reader.step + 2 }
      else
        pure { reader with
          error := some s!"reader: graph invalidated by selecting {selected.id} at step {reader.step} (Owners invariant violated)",
          is_finished := true }

/--
One reading step: pick any surviving node at the current step (Julia's
`first(ids)`), register it and filter. An empty step on a supposedly valid
graph is reported as an error, never skipped.
-/
def read_step! (reader : GPathReader) : IO GPathReader := do
  if reader.is_finished then
    pure reader
  else
    let ids ← getIdsStep reader.gpath.table_lines reader.step
    match ids.toList.head? with
    | none =>
      pure { reader with
        error := some s!"reader: no nodes at step {reader.step}",
        is_finished := true }
    | some selected => register_and_filter! reader selected

partial def read! (reader : GPathReader) : IO GPathReader := do
  if reader.is_finished then
    pure reader
  else
    read! (← read_step! reader)

section Theorems

theorem new_is_finished_is_false (gpath : GPath) :
    (GPathReader.new gpath).is_finished = false := by
  simp [GPathReader.new]

theorem new_solution_is_empty (gpath : GPath) :
    (GPathReader.new gpath).solution.isEmpty := by
  simp [GPathReader.new]

theorem new_error_is_none (gpath : GPath) :
    (GPathReader.new gpath).error = none := by
  simp [GPathReader.new]

end Theorems

section Examples

def run_title_tests : IO Unit := do
  assert! title_ends_literals "FusionNode"
  assert! title_ends_literals "or3=101"
  assert! !(title_ends_literals "7=0")
  assert! !(title_ends_literals "!7=1")

#eval run_title_tests

end Examples

end AbsSat.GraphPath.Reader
