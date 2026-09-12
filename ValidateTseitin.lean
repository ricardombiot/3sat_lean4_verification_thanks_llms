import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.GraphPath.Reader.PathReader
import AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.GraphMap
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader.PathReader
open AbsSat.Db.Machine.Cols.ColTimeline

/-- Evaluate Tseitin formula: (x1 ∨ x2) ∧ (x1 ∨ ¬x3) ∧ (¬x2 ∨ x3) ∧ (x2 ∨ x3) -/
def evaluate_tseitin (assignment : Array Bool) : Bool :=
  if assignment.size < 3 then false
  else
    let x1 := assignment[0]!
    let x2 := assignment[1]!
    let x3 := assignment[2]!

    let clause1 := x1 || x2
    let clause2 := x1 || !x3
    let clause3 := !x2 || x3
    let clause4 := x2 || x3

    clause1 && clause2 && clause3 && clause4

/-- Generate all 2^n assignments -/
def generate_all_assignments (n : Nat) : Array (Array Bool) := do
  let mut assignments : Array (Array Bool) := #[]
  let max_num := 2 ^ n

  for i in [0:max_num] do
    let mut assignment : Array Bool := #[]
    let mut num := i
    for _ in [0:n] do
      assignment := assignment.push (num % 2 == 1)
      num := num / 2
    assignments := assignments.push assignment

  assignments

/-- Brute force: find all satisfying assignments -/
def brute_force_sat (n : Nat := 6) : Array (Array Bool) :=
  let all_assignments := generate_all_assignments n
  all_assignments.filter (fun assignment => evaluate_tseitin assignment)

/-- Convert solution array to binary string -/
def solution_to_binary (solution : Array Bool) : String :=
  String.intercalate "" (solution.toList.map (fun b => if b then "1" else "0"))

/-- Convert binary string to array -/
def binary_to_solution (binary : String) : Array Bool :=
  binary.toList.map (fun c => c == '1') |>.toArray

/-- Main validation -/
def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Tseitin Validation: Reader vs Brute  ║"
  IO.println "║  Force (Correctness & Completeness)   ║"
  IO.println "╚════════════════════════════════════════╝\n"

  -- Step 1: Brute force validation
  IO.println "🔍 STEP 1: Brute Force SAT Solving"
  IO.println "──────────────────────────────────"
  let brute_solutions := brute_force_sat 6
  IO.println s!"✅ Brute force found {brute_solutions.size} solutions out of 64 possible\n"

  IO.println "Brute Force Solutions (first 24):"
  for (idx, solution) in brute_solutions.toList.take 24 |>.mapIdx (fun i s => (i + 1, s)) do
    let binary := solution_to_binary solution
    IO.println s!"  {idx}. {binary}"

  if brute_solutions.size > 24 then
    IO.println s!"  ... ({brute_solutions.size - 24} more)"

  -- Step 2: Reader solutions
  IO.println "\n📖 STEP 2: Reader (Lean 4 Implementation)"
  IO.println "───────────────────────────────────────"

  let cnf_path := "tseitin_test.cnf"
  if !(← System.FilePath.pathExists cnf_path) then
    IO.println s!"Error: {cnf_path} not found"
    return

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! cnf_path

  let machine ← new gmap
  init! machine
  execute_step! machine

  let found_solution ← have_solution machine
  if !found_solution then
    IO.println "❌ Reader found no solution"
    return

  let timeline ← machine.timeline.get
  let current_step ← machine.current_step.get

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
      IO.println s!"✅ Reader found {reader_solutions.size} solutions\n"

      IO.println "Reader Solutions (first 24):"
      for (idx, solution) in reader_solutions.toList.take 24 |>.mapIdx (fun i s => (i + 1, s)) do
        let binary := solution_to_binary solution
        IO.println s!"  {idx}. {binary}"

      if reader_solutions.size > 24 then
        IO.println s!"  ... ({reader_solutions.size - 24} more)"

      -- Step 3: Comparison
      IO.println "\n📊 STEP 3: Validation Results"
      IO.println "────────────────────────────"

      -- Check count match
      if reader_solutions.size == brute_solutions.size then
        IO.println s!"✅ COUNT MATCH: {reader_solutions.size} = {brute_solutions.size}"
      else
        IO.println s!"❌ COUNT MISMATCH: Reader={reader_solutions.size}, Brute={brute_solutions.size}"

      -- Verify all reader solutions are in brute force set
      let mut all_reader_in_brute := true
      for reader_sol in reader_solutions do
        let found := brute_solutions.any (fun brute_sol =>
          reader_sol.toList.zip brute_sol.toList |>.all (fun (r, b) => r == b)
        )
        if !found then
          all_reader_in_brute := false
          let binary := solution_to_binary reader_sol
          IO.println s!"❌ Reader solution NOT in brute force: {binary}"

      if all_reader_in_brute then
        IO.println s!"✅ CORRECTNESS: All {reader_solutions.size} Reader solutions are valid"

      -- Verify all brute solutions are in reader set
      let mut all_brute_in_reader := true
      let mut missing_solutions : Array (Array Bool) := #[]
      for brute_sol in brute_solutions do
        let found := reader_solutions.any (fun reader_sol =>
          reader_sol.toList.zip brute_sol.toList |>.all (fun (r, b) => r == b)
        )
        if !found then
          all_brute_in_reader := false
          missing_solutions := missing_solutions.push brute_sol

      if all_brute_in_reader then
        IO.println s!"✅ COMPLETENESS: Reader found all {brute_solutions.size} solutions"
      else
        IO.println s!"❌ INCOMPLETENESS: Reader missed {missing_solutions.size} solutions:"
        for missing in missing_solutions do
          let binary := solution_to_binary missing
          IO.println s!"   {binary}"

      -- Final verdict
      IO.println "\n🎯 FINAL VERDICT"
      IO.println "───────────────"
      if reader_solutions.size == brute_solutions.size && all_reader_in_brute && all_brute_in_reader then
        IO.println "✅ PERFECT: Reader is correct and complete"
        IO.println "   - All solutions are valid (satisfy formula)"
        IO.println "   - All solutions were found (no omissions)"
        IO.println "   - No extra solutions (no false positives)"
      else
        IO.println "❌ VALIDATION FAILED"
        if !all_reader_in_brute then
          IO.println "   - Some reader solutions don't satisfy formula"
        if !all_brute_in_reader then
          IO.println "   - Some valid solutions were missed"

  IO.println "\n══════════════════════════════════════════════════"
  IO.println "Validation complete"
