-- PathReader: Extract solutions from GPath certificate set
import AbsSat.GraphPath.GraphPath
import AbsSat.GraphPath.Reader.PathReaderFilter
import AbsSat.Utils.Alias

namespace AbsSat.GraphPath.Reader.PathReader

open AbsSat.GraphPath
open AbsSat.Utils.Alias
open AbsSat.Db.Path.Cols.PathColLines
open AbsSat.Db.Path.Docs.PathDocNode

structure GPathReader where
  gpath : GPath
  solution : Array Bool
  step : Int
  last_selected : Option PathNodeId
  is_finished : Bool

/-- Create a new reader for a GPath -/
def new (gpath : GPath) : GPathReader := {
  gpath := gpath
  solution := #[]
  step := 0
  last_selected := none
  is_finished := false
}

/-- Extract literal value from node and update solution -/
def register_selection! (solution : Array Bool) (node : PathDocNode) : (Array Bool × Bool) :=
  let title := node.title

  -- Check if this is a terminal node (clause evaluation or fusion)
  if title.contains "or" || title.contains "FusionNode" then
    (solution, true)  -- Finished: reached clause or fusion
  else
    -- Extract literal value from node ID
    -- Literals are: 0 = false, 1 = true
    let literal_value := if node.id.id.index == 0 then false else true
    let new_solution := solution.push literal_value
    (new_solution, false)  -- Continue reading

/-- Read one step: select node, register value, advance -/
def read_step! (reader : GPathReader) : IO GPathReader := do
  if reader.is_finished then
    pure reader
  else
    -- Step 1: Get line at current step
    let table ← reader.gpath.table_lines.table.get
    match table.get? reader.step with
    | none =>
        pure { reader with is_finished := true }
    | some line =>
        -- Step 2: Get nodes from this line
        let nodes_table ← line.table.get
        let nodes := nodes_table.toList

        if nodes.isEmpty then
          pure { reader with is_finished := true }
        else
          -- Step 3: Select first node
          match nodes.head? with
          | none =>
              pure { reader with is_finished := true }
          | some (selected_id, selected_node) =>
              -- Step 4: Register selection (extract literal value)
              let (updated_solution, finished) := register_selection! reader.solution selected_node

              -- Step 5: Move to next step
              let next_step := reader.step + 2

              pure {
                reader with
                solution := updated_solution
                step := next_step
                last_selected := some selected_id
                is_finished := finished
              }

/-- Read one step: return all possible next readers (for multi-path traversal) -/
def read_step_all! (reader : GPathReader) : IO (Array GPathReader) := do
  if reader.is_finished then
    pure #[reader]
  else
    -- Step 1: Get line at current step
    let table ← reader.gpath.table_lines.table.get
    match table.get? reader.step with
    | none =>
        pure #[{ reader with is_finished := true }]
    | some line =>
        -- Step 2: Get nodes from this line
        let nodes_table ← line.table.get
        let nodes := nodes_table.toList

        if nodes.isEmpty then
          pure #[{ reader with is_finished := true }]
        else
          -- Step 3: Create reader for each node
          let mut next_readers : Array GPathReader := #[]

          for (selected_id, selected_node) in nodes do
            -- CLONE the GPath for this branch (each branch gets its own filtered copy)
            let branch_gpath ← GPath.clone reader.gpath

            -- Register selection (extract literal value)
            let (updated_solution, finished) := register_selection! reader.solution selected_node

            -- Step 4: Filter the CLONED GPath based on selected node
            if !finished then
              let requires : Std.HashSet NodeId := {selected_id.id}
              AbsSat.GraphPath.filter! branch_gpath requires

            -- Step 5: Move to next step
            let next_step := reader.step + 2

            let next_reader := {
              reader with
              gpath := branch_gpath
              solution := updated_solution
              step := next_step
              last_selected := some selected_id
              is_finished := finished
            }

            next_readers := next_readers.push next_reader

          pure next_readers

/-- Full read: execute steps until completion -/
def read! (reader : GPathReader) : IO GPathReader := do
  let mut current := reader
  while !current.is_finished do
    current ← read_step! current
  pure current

/-- Extract all solutions by exploring all valid paths in GPath -/
def read_all_solutions! (gpath : GPath) : IO (Array (Array Bool)) := do
  let mut solutions : Array (Array Bool) := #[]
  let mut current_readers : Array GPathReader := #[new gpath]

  -- Breadth-first exploration with filtering at each step
  while !current_readers.isEmpty do
    let mut next_readers : Array GPathReader := #[]

    for reader in current_readers do
      if reader.is_finished then
        -- Found complete solution
        if !solutions.contains reader.solution then
          solutions := solutions.push reader.solution
      else
        -- Get all next readers and filter
        let next_states ← read_step_all! reader

        for next_reader in next_states do
          if next_reader.is_finished then
            if !solutions.contains next_reader.solution then
              solutions := solutions.push next_reader.solution
          else
            next_readers := next_readers.push next_reader

    current_readers := next_readers

  pure solutions

/-- Print solution in human-readable format -/
def solution_to_string (solution : Array Bool) : String :=
  let parts := solution.mapIdx (fun i val =>
    let var_num := i + 1
    if val then s!"x{var_num}=T" else s!"x{var_num}=F"
  )
  String.intercalate ", " parts.toList

/-- Statistics about reading process -/
def print_stats! (solutions : Array (Array Bool)) : IO Unit := do
  IO.println s!"\n📊 Reader Statistics:"
  IO.println s!"  Total solutions found: {solutions.size}"

  if !solutions.isEmpty then
    let first_size := solutions[0]!.size
    IO.println s!"  Variables per solution: {first_size}"

    for (idx, solution) in solutions.toList.mapIdx (fun idx sol => (idx + 1, sol)) do
      let sol_str := solution_to_string solution
      IO.println s!"    Solution {idx}: {sol_str}"

end AbsSat.GraphPath.Reader.PathReader
