import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader.PathReader
open AbsSat.Db.Machine.Cols.ColTimeline

/-- Evaluate Graph Coloring: 5 vertices, 3 colors, edges: (1,2),(1,3),(2,3),(2,4),(3,4),(4,5)
    Variables: x_ic = vertex i has color c (i=1..5, c=1..3)
    x1-x3=v1, x4-x6=v2, x7-x9=v3, x10-x12=v4, x13-x15=v5
-/
def evaluate_graph_coloring (assignment : Array Bool) : Bool :=
  if assignment.size < 15 then false
  else
    -- Vertex 1 (colors)
    let v1c1 := assignment[0]!
    let v1c2 := assignment[1]!
    let v1c3 := assignment[2]!
    -- Vertex 2 (colors)
    let v2c1 := assignment[3]!
    let v2c2 := assignment[4]!
    let v2c3 := assignment[5]!
    -- Vertex 3 (colors)
    let v3c1 := assignment[6]!
    let v3c2 := assignment[7]!
    let v3c3 := assignment[8]!
    -- Vertex 4 (colors)
    let v4c1 := assignment[9]!
    let v4c2 := assignment[10]!
    let v4c3 := assignment[11]!
    -- Vertex 5 (colors)
    let v5c1 := assignment[12]!
    let v5c2 := assignment[13]!
    let v5c3 := assignment[14]!

    -- Each vertex has at least one color
    let v1_colored := v1c1 || v1c2 || v1c3
    let v2_colored := v2c1 || v2c2 || v2c3
    let v3_colored := v3c1 || v3c2 || v3c3
    let v4_colored := v4c1 || v4c2 || v4c3
    let v5_colored := v5c1 || v5c2 || v5c3

    -- No vertex has more than one color
    let v1_one := (!v1c1 || !v1c2) && (!v1c1 || !v1c3) && (!v1c2 || !v1c3)
    let v2_one := (!v2c1 || !v2c2) && (!v2c1 || !v2c3) && (!v2c2 || !v2c3)
    let v3_one := (!v3c1 || !v3c2) && (!v3c1 || !v3c3) && (!v3c2 || !v3c3)
    let v4_one := (!v4c1 || !v4c2) && (!v4c1 || !v4c3) && (!v4c2 || !v4c3)
    let v5_one := (!v5c1 || !v5c2) && (!v5c1 || !v5c3) && (!v5c2 || !v5c3)

    -- Adjacent vertices different colors
    -- Edges: (1,2), (1,3), (2,3), (2,4), (3,4), (4,5)
    -- Color 1
    let edges_c1 := (!v1c1 || !v2c1) && (!v1c1 || !v3c1) && (!v2c1 || !v3c1) &&
                    (!v2c1 || !v4c1) && (!v3c1 || !v4c1) && (!v4c1 || !v5c1)
    -- Color 2
    let edges_c2 := (!v1c2 || !v2c2) && (!v1c2 || !v3c2) && (!v2c2 || !v3c2) &&
                    (!v2c2 || !v4c2) && (!v3c2 || !v4c2) && (!v4c2 || !v5c2)
    -- Color 3
    let edges_c3 := (!v1c3 || !v2c3) && (!v1c3 || !v3c3) && (!v2c3 || !v3c3) &&
                    (!v2c3 || !v4c3) && (!v3c3 || !v4c3) && (!v4c3 || !v5c3)

    v1_colored && v2_colored && v3_colored && v4_colored && v5_colored &&
    v1_one && v2_one && v3_one && v4_one && v5_one &&
    edges_c1 && edges_c2 && edges_c3

/-- Convert number to binary assignment -/
def number_to_assignment (num : Nat) (n : Nat) : Array Bool :=
  (List.range n).map (fun i => (num / (2 ^ i)) % 2 == 1) |>.toArray

/-- Generate all 2^n assignments -/
def generate_all_assignments (n : Nat) : Array (Array Bool) :=
  (List.range (2 ^ n)).map (fun i => number_to_assignment i n) |>.toArray

/-- Brute force: find all satisfying assignments -/
def brute_force_sat (n : Nat := 15) : Array (Array Bool) :=
  let all_assignments := generate_all_assignments n
  all_assignments.filter (fun assignment => evaluate_graph_coloring assignment)

/-- Convert solution array to binary string -/
def solution_to_binary (solution : Array Bool) : String :=
  String.intercalate "" (solution.toList.map (fun b => if b then "1" else "0"))

/-- Main validation -/
def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Graph Coloring Validation           ║"
  IO.println "║  5 vertices, 3 colors, 6 edges      ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Step 1: Brute force validation
  IO.println "🔍 STEP 1: Brute Force SAT Solving"
  IO.println "──────────────────────────────────"
  let brute_solutions := brute_force_sat 15
  IO.println s!"✅ Brute force found {brute_solutions.size} solutions out of 32768 possible\n"

  if brute_solutions.isEmpty then
    IO.println "❌ No valid colorings found (formula unsatisfiable)"
  else
    IO.println "✅ Valid 3-colorings found:"
    for (idx, solution) in brute_solutions.toList.take 5 |>.mapIdx (fun i s => (i + 1, s)) do
      let binary := solution_to_binary solution
      IO.println s!"  {idx}. {binary}"
    if brute_solutions.size > 5 then
      IO.println s!"  ... ({brute_solutions.size - 5} more)"

  -- Step 2: Reader solutions
  IO.println "\n📖 STEP 2: Reader (Lean 4 Implementation)"
  IO.println "───────────────────────────────────────"

  let cnf_path := "graph_coloring_3col.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found"
    return

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path

  let machine ← new gmap
  init! machine
  execute_step! machine

  let found_solution ← have_solution machine
  let current_step ← machine.current_step.get

  IO.println s!"✅ Machine complete: step={current_step}, SAT={found_solution}\n"

  if !found_solution then
    IO.println "❌ Reader found no valid coloring"
  else
    IO.println "✅ Reader found valid coloring"

    let timeline ← machine.timeline.get

    let first_gpath_ref ← IO.mkRef (none : Option GPath)
    for_each_gpath timeline current_step (fun gpath => do
      let current ← first_gpath_ref.get
      if current.isNone then
        first_gpath_ref.set (some gpath)
    )
    let first_gpath ← first_gpath_ref.get

    match first_gpath with
    | none =>
        IO.println "❌ No GPath found"
    | some gpath =>
        let reader_solutions ← read_all_solutions! gpath
        IO.println s!"Reader extracted: {reader_solutions.size} colorings"

        if !reader_solutions.isEmpty then
          IO.println "\nFirst 5 Reader colorings:"
          for (idx, solution) in reader_solutions.toList.take 5 |>.mapIdx (fun i s => (i + 1, s)) do
            let binary := solution_to_binary solution
            IO.println s!"  {idx}. {binary}"
          if reader_solutions.size > 5 then
            IO.println s!"  ... ({reader_solutions.size - 5} more)"

  -- Step 3: Comparison
  IO.println "\n📊 STEP 3: Validation Results"
  IO.println "────────────────────────────"

  if brute_solutions.isEmpty then
    if !found_solution then
      IO.println "✅ Both agree: No valid 3-coloring exists"
    else
      IO.println "❌ Mismatch: Reader found coloring but brute force didn't"
  else
    if !found_solution then
      IO.println "❌ Mismatch: Brute force found colorings but Reader didn't"
    else
      IO.println "✅ Both found valid colorings"
      IO.println s!"   Brute force: {brute_solutions.size} colorings"

  IO.println "\n════════════════════════════════════════════════════"
  IO.println "Graph coloring validation complete"
