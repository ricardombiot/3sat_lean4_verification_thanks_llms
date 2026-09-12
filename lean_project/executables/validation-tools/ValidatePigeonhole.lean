import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader.PathReader
open AbsSat.Db.Machine.Cols.ColTimeline

/-- Evaluate PHP(2,3): 3 pigeons in 2 holes
    Variables: x_ij = pigeon i in hole j (i=1..3, j=1..2)
    x1=x11, x2=x12, x3=x21, x4=x22, x5=x31, x6=x32
    Constraints:
    1. Each pigeon in at least one hole
    2. At most one pigeon per hole
-/
def evaluate_pigeonhole (assignment : Array Bool) : Bool :=
  if assignment.size < 6 then false
  else
    let x11 := assignment[0]!  -- pigeon 1 in hole 1
    let x12 := assignment[1]!  -- pigeon 1 in hole 2
    let x21 := assignment[2]!  -- pigeon 2 in hole 1
    let x22 := assignment[3]!  -- pigeon 2 in hole 2
    let x31 := assignment[4]!  -- pigeon 3 in hole 1
    let x32 := assignment[5]!  -- pigeon 3 in hole 2

    -- 1. Each pigeon in at least one hole
    let pigeon1 := x11 || x12
    let pigeon2 := x21 || x22
    let pigeon3 := x31 || x32

    -- 2. At most one pigeon per hole
    let hole1_p1_p2 := !x11 || !x21
    let hole1_p1_p3 := !x11 || !x31
    let hole1_p2_p3 := !x21 || !x31
    let hole2_p1_p2 := !x12 || !x22
    let hole2_p1_p3 := !x12 || !x32
    let hole2_p2_p3 := !x22 || !x32

    pigeon1 && pigeon2 && pigeon3 &&
    hole1_p1_p2 && hole1_p1_p3 && hole1_p2_p3 &&
    hole2_p1_p2 && hole2_p1_p3 && hole2_p2_p3

/-- Convert number to binary assignment -/
def number_to_assignment (num : Nat) (n : Nat) : Array Bool :=
  (List.range n).map (fun i => (num / (2 ^ i)) % 2 == 1) |>.toArray

/-- Generate all 2^n assignments -/
def generate_all_assignments (n : Nat) : Array (Array Bool) :=
  (List.range (2 ^ n)).map (fun i => number_to_assignment i n) |>.toArray

/-- Brute force: find all satisfying assignments -/
def brute_force_sat (n : Nat := 6) : Array (Array Bool) :=
  let all_assignments := generate_all_assignments n
  all_assignments.filter (fun assignment => evaluate_pigeonhole assignment)

/-- Convert solution array to binary string -/
def solution_to_binary (solution : Array Bool) : String :=
  String.intercalate "" (solution.toList.map (fun b => if b then "1" else "0"))

/-- Main validation -/
def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Pigeonhole Formula Validation: PHP   ║"
  IO.println "║  3 Pigeons in 2 Holes (Unsatisfiable)║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Step 1: Brute force validation
  IO.println "🔍 STEP 1: Brute Force SAT Solving"
  IO.println "──────────────────────────────────"
  let brute_solutions := brute_force_sat 6
  IO.println s!"✅ Brute force found {brute_solutions.size} solutions out of 64 possible\n"

  if brute_solutions.isEmpty then
    IO.println "📌 Key Finding: PHP(2,3) is UNSATISFIABLE"
    IO.println "   (Cannot place 3 pigeons in 2 holes)"
  else
    IO.println "Solutions found (unexpected for PHP(2,3)):"
    for (idx, solution) in brute_solutions.toList.mapIdx (fun i s => (i + 1, s)) do
      let binary := solution_to_binary solution
      IO.println s!"  {idx}. {binary}"

  -- Step 2: Reader solutions
  IO.println "\n📖 STEP 2: Reader (Lean 4 Implementation)"
  IO.println "───────────────────────────────────────"

  let cnf_path := "pigeonhole.cnf"
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
    IO.println "✅ Correct: Reader found UNSATISFIABLE (no solution)"
  else
    IO.println "⚠️  Warning: Reader found solution (expected UNSATISFIABLE)"

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
        IO.println s!"Reader extracted: {reader_solutions.size} solutions"

        if !reader_solutions.isEmpty then
          IO.println "\nReader Solutions:"
          for (idx, solution) in reader_solutions.toList.take 10 |>.mapIdx (fun i s => (i + 1, s)) do
            let binary := solution_to_binary solution
            IO.println s!"  {idx}. {binary}"

  -- Step 3: Comparison
  IO.println "\n📊 STEP 3: Validation Results"
  IO.println "────────────────────────────"

  if brute_solutions.isEmpty then
    IO.println "✅ PHP(2,3) is UNSATISFIABLE (proven by brute force)"
    if !found_solution then
      IO.println "✅ Reader agrees: UNSATISFIABLE"
      IO.println "\n🎯 FINAL VERDICT"
      IO.println "───────────────"
      IO.println "✅ PERFECT MATCH: Reader correctly identifies UNSAT formula"
    else
      IO.println "❌ Reader disagrees: Found SAT"
      IO.println "\n🎯 FINAL VERDICT"
      IO.println "───────────────"
      IO.println "❌ MISMATCH: Reader incorrectly marked as SAT"
  else
    IO.println "⚠️  Unexpected: Brute force found satisfying assignments"

  IO.println "\n══════════════════════════════════════════════════"
  IO.println "Pigeonhole validation complete"
