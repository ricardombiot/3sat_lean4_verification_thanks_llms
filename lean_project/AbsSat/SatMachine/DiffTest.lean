-- lean_project/AbsSat/SatMachine/DiffTest.lean
import AbsSat.SatMachine.SatMachine
import AbsSat.GraphMap.ImportCnf
import AbsSat.Utils.ExhaustiveSolver
import AbsSat.GraphPath.Reader.PathExpReader
import AbsSat.GraphPath.Model.MirrorTest
import Std.Data.HashSet

/-!
Randomized differential testing: SatMachine (+ Owners-based reading) against
the brute-force `ExhaustiveSolver` oracle.

For each random 3SAT instance the harness compares:
1. the SAT/UNSAT verdict, and
2. when SAT, the *complete set of solutions* read out of the final gpaths via
   `GPathExpReader` against the oracle's enumeration.

This is the empirical shield recommended in `formal_bridge_owners_runpure.md`
§6.3: if the "no zombies"/Helly invariant (lemma L6) has a counterexample, or
the Owners compression ever loses/invents a configuration, it shows up here as
a set mismatch or a reader invariant-violation — long before investing in the
Lean bridge proof. Failing instances are dumped to `difftest_failure_<k>.cnf`
and are fully reproducible from the (seed, case count) pair.
-/

namespace AbsSat.SatMachine.DiffTest

open AbsSat.Utils.Alias
open AbsSat.SatMachine
open AbsSat.GraphPath
open AbsSat.GraphPath.Reader

-- ============================================================
-- Deterministic RNG (64-bit LCG, Knuth constants)
-- ============================================================

structure Rng where
  state : UInt64

def Rng.ofSeed (seed : Nat) : Rng := { state := UInt64.ofNat (seed + 88172645463325252) }

def Rng.next (rng : Rng) : Rng × Nat :=
  let s := rng.state * 6364136223846793005 + 1442695040888963407
  ({ state := s }, (s >>> 33).toNat)

/-- Uniform-ish value in `[0, n)`. `n` must be positive. -/
def Rng.below (rng : Rng) (n : Nat) : Rng × Nat :=
  let (rng, v) := rng.next
  (rng, v % n)

-- ============================================================
-- Random 3SAT instance generation
-- ============================================================

/-- Pick `need` distinct variables from `1..n` (requires `n ≥ need`). -/
partial def pick_distinct_vars (rng : Rng) (n need : Nat) (acc : List Nat) : Rng × List Nat :=
  if acc.length == need then
    (rng, acc)
  else
    let (rng, v) := rng.below n
    let candidate := v + 1
    if acc.contains candidate then
      pick_distinct_vars rng n need acc
    else
      pick_distinct_vars rng n need (candidate :: acc)

def gen_clause (rng : Rng) (nVars : Nat) : Rng × String :=
  let (rng, vars) := pick_distinct_vars rng nVars 3 []
  let (rng, line) := vars.foldl (fun (st : Rng × String) v =>
    let (rng, acc) := st
    let (rng, sign) := rng.below 2
    let lit := if sign == 0 then s!"{v}" else s!"-{v}"
    (rng, if acc.isEmpty then lit else s!"{acc} {lit}")
  ) (rng, "")
  (rng, s!"{line} 0")

def gen_cnf (rng : Rng) (nVars nClauses : Nat) : Rng × String :=
  let (rng, body) := (List.range nClauses).foldl (fun (st : Rng × String) _ =>
    let (rng, acc) := st
    let (rng, clause) := gen_clause rng nVars
    (rng, acc ++ clause ++ "\n")
  ) (rng, "")
  (rng, s!"p cnf {nVars} {nClauses}\n" ++ body)

-- ============================================================
-- Solution-set plumbing
-- ============================================================

def solution_key (solution : Array Bool) : String :=
  String.ofList (solution.toList.map (fun b => if b then '1' else '0'))

def keys_of (solutions : List (Array Bool)) : Std.HashSet String :=
  solutions.foldl (fun s sol => s.insert (solution_key sol)) {}

def set_diff (a b : Std.HashSet String) : List String :=
  a.toList.filter (fun k => !b.contains k)

/-- Collect the gpaths parked at the machine's final timeline step. -/
def final_gpaths (machine : MSat) : IO (List GPath) := do
  let current ← machine.current_step.get
  let timeline ← machine.timeline.get
  let acc ← IO.mkRef ([] : List GPath)
  AbsSat.Db.Machine.Cols.ColTimeline.for_each_gpath timeline current (fun gpath =>
    acc.modify (gpath :: ·))
  acc.get

/-- Read every configuration out of every final gpath (deduplicated union). -/
def machine_solution_keys (machine : MSat) : IO (Except String (Std.HashSet String)) := do
  let gpaths ← final_gpaths machine
  let mut keys : Std.HashSet String := {}
  for gpath in gpaths do
    match ← GPathExpReader.read_all_solutions gpath with
    | .error e => return .error e
    | .ok solutions =>
      for sol in solutions do
        keys := keys.insert (solution_key sol)
  pure (.ok keys)

-- ============================================================
-- One differential case
-- ============================================================

structure CaseResult where
  ok : Bool
  message : String

def run_case (cnf : String) (tmp_path : String) : IO CaseResult := do
  IO.FS.writeFile tmp_path cnf

  -- Oracle
  let solver ← AbsSat.Utils.ExhaustiveSolver.new tmp_path
  AbsSat.Utils.ExhaustiveSolver.run! solver
  let oracle_solutions ← solver.listSolutions.get
  let oracle_keys := keys_of (oracle_solutions.toList.map id)
  let oracle_sat := !oracle_solutions.isEmpty

  -- Machine
  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! tmp_path
  let machine ← AbsSat.SatMachine.new gmap
  AbsSat.SatMachine.run! machine
  let machine_sat ← have_solution machine

  if machine_sat != oracle_sat then
    return { ok := false,
             message := s!"VERDICT mismatch: machine={machine_sat} oracle={oracle_sat}" }

  if !machine_sat then
    match AbsSat.GraphPath.Model.MirrorTest.mirrorSolutions gmap with
    | .error e =>
      return { ok := false, message := s!"MIRROR reader error on UNSAT instance: {e}" }
    | .ok mirror_solutions =>
      if mirror_solutions.isEmpty then
        return { ok := true, message := "UNSAT agreed (mirror agreed)" }
      else
        return { ok := false,
                 message := s!"MIRROR claims SAT ({mirror_solutions.length} solutions) on UNSAT instance" }

  match ← machine_solution_keys machine with
  | .error e =>
    return { ok := false, message := s!"READER error: {e}" }
  | .ok machine_keys =>
    let missing := set_diff oracle_keys machine_keys
    let invented := set_diff machine_keys oracle_keys
    if !(missing.isEmpty && invented.isEmpty) then
      return { ok := false,
               message := s!"SOLUTION SET mismatch: missing={missing} invented={invented} (machine={machine_keys.size}, oracle={oracle_keys.size})" }

    -- Third band: the pure mirror GPathM (machine loop + reader), which the
    -- bridge proofs will reason about. It must agree with the oracle too.
    match AbsSat.GraphPath.Model.MirrorTest.mirrorSolutions gmap with
    | .error e =>
      return { ok := false, message := s!"MIRROR reader error: {e}" }
    | .ok mirror_solutions =>
      let mirror_keys := keys_of mirror_solutions
      let m_missing := set_diff oracle_keys mirror_keys
      let m_invented := set_diff mirror_keys oracle_keys
      if m_missing.isEmpty && m_invented.isEmpty then
        return { ok := true,
                 message := s!"SAT agreed, {machine_keys.size} solutions (mirror agreed)" }
      else
        return { ok := false,
                 message := s!"MIRROR solution set mismatch: missing={m_missing} invented={m_invented} (mirror={mirror_keys.size}, oracle={oracle_keys.size})" }

-- ============================================================
-- Driver
-- ============================================================

def run_diff_tests (cases seed : Nat) : IO UInt32 := do
  IO.println s!"--- Differential testing: SatMachine+Reader vs ExhaustiveSolver ---"
  IO.println s!"cases={cases} seed={seed}"

  let mut rng := Rng.ofSeed seed
  let mut failures := 0
  let mut sat_count := 0
  let mut unsat_count := 0

  for idx in [0:cases] do
    -- nVars in 3..7. Two density regimes: the default 1..4n spans under- to
    -- critically-constrained (mostly SAT, exercising the solution-set
    -- comparison); every third case uses 4n..6n, past the ~4.26n phase
    -- transition, so the UNSAT verdict path gets real coverage too.
    let (rng1, nv) := rng.below 5
    let nVars := 3 + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3

    let result ← run_case cnf "difftest_tmp.cnf"
    if result.ok then
      if result.message.startsWith "SAT" then
        sat_count := sat_count + 1
      else
        unsat_count := unsat_count + 1
    else
      failures := failures + 1
      let failure_path := s!"difftest_failure_{idx}.cnf"
      IO.FS.writeFile failure_path cnf
      IO.println s!"❌ case {idx} (vars={nVars}, clauses={nClauses}): {result.message}"
      IO.println s!"   instance saved to {failure_path}:"
      IO.println cnf

  IO.println s!"--- Differential testing done: {cases - failures}/{cases} agreed ({sat_count} SAT, {unsat_count} UNSAT), {failures} failures ---"
  if failures == 0 then
    IO.println "Differential testing Passed! ✅"
    pure 0
  else
    IO.println "Differential testing FAILED ❌"
    pure 1

end AbsSat.SatMachine.DiffTest
