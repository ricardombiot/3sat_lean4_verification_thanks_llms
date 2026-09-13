-- lean_project/AbsSat/GraphPath/Reader/PathExpReader.lean
import AbsSat.GraphPath.GraphPath
import AbsSat.GraphPath.Reader.PathReader
import Std.Data.HashMap

/-!
Port of `docs/original_julia/src/graph_path/reader/path_exp_reader.jl`.

The exponential reader enumerates *every* configuration represented by a
`GPath`: instead of picking one node per step, it forks one derived reader
(with a cloned graph) per candidate at the current step, filters each fork by
its selection, and collects the solutions of the forks that reach the end of
the literal block.

One deliberate deviation from Julia: forks are per distinct *map* `NodeId`,
not per `PathNodeId`. Several `PathNodeId`s at the same step can share the
same map id (same literal value reached from different parents), and
`filter!` compares by map id — so per-`PathNodeId` forks produce
byte-identical filtered graphs and duplicate solutions. Deduplicating at fork
time is equivalent and keeps the enumeration linear in the number of distinct
configurations.
-/

namespace AbsSat.GraphPath.Reader

open AbsSat.Utils.Alias
open AbsSat.GraphPath
open AbsSat.Db.Path.Cols.PathColLines
open AbsSat.Db.Path.Docs.PathDocNode
open AbsSat.GraphPath.Reader.PathReader

structure GPathExpReader where
  list_readers : List GPathReader
  list_solutions : List (Array Bool)
  error : Option String
  is_finished : Bool

namespace GPathExpReader

def new (gpath : GPath) : GPathExpReader :=
  let reader_seed := PathReader.new gpath
  { list_readers := [reader_seed],
    list_solutions := [],
    error := none,
    is_finished := false }

/--
Fork one derived reader per distinct map id at the reader's current step,
each on a cloned graph, already registered and filtered by its selection.
The seed reader's graph is never mutated (clones happen before filtering),
mirroring Julia's `deepcopy` in `select_and_derive!`. An empty step, or a
filter that invalidates a fork, is reported as an error so completeness bugs
cannot die silently.
-/
def select_and_derive! (reader : GPathReader) : IO (Except String (List GPathReader)) := do
  let table ← reader.gpath.table_lines.table.get
  match table.get? reader.step with
  | none => pure (.ok [{ reader with is_finished := true }])
  | some line =>
    let nodes := (← line.table.get).toList

    let mut reps : Std.HashMap NodeId (PathNodeId × PathDocNode) := {}
    for (id, node) in nodes do
      if !reps.contains id.id then
        reps := reps.insert id.id (id, node)

    if reps.isEmpty then
      return .error s!"exp_reader: no nodes at step {reader.step}"

    let mut derived : List GPathReader := []
    for (_, (selected_id, selected_node)) in reps.toList do
      let cloned ← GPath.clone reader.gpath
      let (solution, finished) := register_selection! reader.solution selected_node
      if !finished then
        let requires : Std.HashSet NodeId := {selected_id.id}
        AbsSat.GraphPath.filter! cloned requires
        if !(← cloned.is_valid.get) then
          return .error s!"exp_reader: filtering a fork invalidated the graph at step {reader.step}"
      let fork := { reader with
        gpath := cloned
        solution := solution
        step := reader.step + 2
        last_selected := some selected_id
        is_finished := finished }
      derived := fork :: derived
    pure (.ok derived)

/--
Drain the worklist of readers: finished forks contribute their solution,
unfinished forks derive further. Any errored fork aborts the enumeration with
its message — an errored fork means the Owners invariant broke mid-read,
which is a finding, not a case to skip.
-/
partial def read! (exp_reader : GPathExpReader) : IO GPathExpReader := do
  match exp_reader.list_readers with
  | [] => pure { exp_reader with is_finished := true }
  | reader :: rest =>
    if reader.is_finished then
      read! { exp_reader with
        list_readers := rest,
        list_solutions := reader.solution :: exp_reader.list_solutions }
    else
      match ← select_and_derive! reader with
      | .error e => pure { exp_reader with error := some e, is_finished := true }
      | .ok derived => read! { exp_reader with list_readers := derived ++ rest }

/--
Enumerate every configuration represented by `gpath`. Returns the list of
solutions (one `Array Bool` per configuration, one bit per variable in
variable order) or the first invariant-violation message encountered.
-/
def read_all_solutions (gpath : GPath) : IO (Except String (List (Array Bool))) := do
  let exp_reader ← read! (new gpath)
  match exp_reader.error with
  | some e => pure (.error e)
  | none => pure (.ok exp_reader.list_solutions)

section Theorems

theorem new_is_finished_is_false (gpath : GPath) :
    (new gpath).is_finished = false := by
  simp [new]

theorem new_list_solutions_is_empty (gpath : GPath) :
    (new gpath).list_solutions.isEmpty := by
  simp [new]

theorem new_list_readers_has_one_element (gpath : GPath) :
    (new gpath).list_readers.length = 1 := by
  simp [new]

theorem new_error_is_none (gpath : GPath) :
    (new gpath).error = none := by
  simp [new]

end Theorems

end GPathExpReader

end AbsSat.GraphPath.Reader
