import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.GraphMap
import AbsSat.GraphMap.ImportCnf
import AbsSat.Utils.Alias
import AbsSat.Utils.ExhaustiveSolver
import AbsSat.Db.Map.Cols.MapColLines

namespace AbsSat.SatMachine.Verification

open AbsSat.SatMachine
open AbsSat.GraphMap.GraphMap
open AbsSat.Utils.Alias
open AbsSat.Db.Map.Cols.MapColLines

-- === Pure Logic Theorems ===

-- 1. close_vars! Structural Theorems
-- Since close_vars! relies on make_fusion_node!, which pushes nodes,
-- we must establish basic properties of these pure operations.

theorem close_vars_increments_step_if_vars (gmap : GMap) :
  gmap.stage = "vars" -> (close_vars! gmap).step = gmap.step + 1 := by
  intro h
  simp [close_vars!, make_fusion_node!, h]

theorem close_vars_updates_stage (gmap : GMap) :
  gmap.stage = "vars" -> (close_vars! gmap).stage = "gates" := by
  intro h
  simp [close_vars!, h]

theorem close_vars_noop_if_not_vars (gmap : GMap) :
  gmap.stage ≠ "vars" -> (close_vars! gmap) = gmap := by
  intro h
  unfold close_vars!
  split <;> try simp_all

-- 2. close_gates! Structural Theorems

theorem close_gates_updates_stage (gmap : GMap) :
  gmap.stage = "gates" -> (close_gates! gmap).stage = "end" := by
  intro h
  simp [close_gates!, h]

-- === Runtime Assertions for Verification ===

def verification_tests : IO Unit := do
  IO.println "Running Verification Theorems (Runtime Checked)..."

  -- 1. GMap Step Increase invariant
  let gmap ← AbsSat.GraphMap.GraphMap.new
  assert! gmap.step == 0

  let gmap ← add_var! gmap "A"
  assert! gmap.step == 2 -- "Adding 1 var should increase step by 2 (Positive + Negative layer)"

  let gmap ← add_var! gmap "B"
  assert! gmap.step == 4

  -- 2. Close Vars invariant (Reflects pure theorems above)
  let gmap := close_vars! gmap
  assert! gmap.stage == "gates"
  assert! gmap.step == 5 -- "Closing vars adds FusionNode"

  -- 3. Add Gate invariant
  let gmap ← add_gate! gmap "A" "B" "A"
  assert! gmap.step == 6 -- "Adding gate adds 1 step"
  assert! gmap.clausule_counter == 1

  -- 4. Machine Init invariant
  let machine ← AbsSat.SatMachine.new gmap
  AbsSat.SatMachine.init! machine

  let timeline ← machine.timeline.get
  -- Step 0 should have 2 paths (corresponding to A_pos=0, A_pos=1)
  let count := AbsSat.Db.Machine.Cols.ColTimeline.get_counter_graphs_step timeline 0
  assert! count == 2 -- s!"Expected 2 initial paths, got {count}"

  IO.println "Verification Theorems Passed! ✅"

/--
Cross-check `SatMachine`'s verdict on a CNF file against `ExhaustiveSolver`
(the independently-implemented, brute-force oracle): both must agree on
whether the instance is satisfiable. This is the regression test that would
have caught the Owners filter never invalidating a broken graph, since that
bug made `SatMachine` report SAT unconditionally.
-/
def cross_validate_cnf! (label : String) (path : String) : IO Unit := do
  IO.println s!"Cross-validating {label} ({path})..."

  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! path
  let machine ← AbsSat.SatMachine.new gmap
  AbsSat.SatMachine.run! machine
  let machine_result ← AbsSat.SatMachine.have_solution machine

  let solver ← AbsSat.Utils.ExhaustiveSolver.new path
  AbsSat.Utils.ExhaustiveSolver.run! solver
  let solutions ← solver.listSolutions.get
  let solver_result := !solutions.isEmpty

  IO.println s!"  SatMachine={machine_result}, ExhaustiveSolver={solver_result}"
  assert! machine_result == solver_result

def cross_validation_tests : IO Unit := do
  IO.println "\n--- Cross-validating SatMachine against ExhaustiveSolver ---"
  cross_validate_cnf! "UNSAT (all 8 sign combinations over 3 vars)" "test_unsat.cnf"
  cross_validate_cnf! "SAT (4 vars, overlapping clauses)" "test_sat_medium.cnf"
  IO.println "Cross-validation Passed! ✅"

end AbsSat.SatMachine.Verification
