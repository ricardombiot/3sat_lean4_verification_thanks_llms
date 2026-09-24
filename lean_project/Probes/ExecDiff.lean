import AbsSat.SatMachine.DiffTest

/-! # `exec-diff`: the IO executable against the exhaustive oracle, without the model band

`diffTest` also runs the pure model (`MirrorTest`), which with the review mirror became too slow on
some small UNSAT cases (a 7-variable case: 104 s before the mirror, more than an hour after). To
validate the executable itself (plan `review_simetrico.md` B4: two-phase clean + mirror), this runs
the same generator and compares only the executable (verdict and read solution set) with the oracle.

    lake exe exec-diff [cases] [seed]
-/

open AbsSat.SatMachine.DiffTest

def main (args : List String) : IO UInt32 := do
  let cases := (args[0]?.bind (·.toNat?)).getD 100
  let seed := (args[1]?.bind (·.toNat?)).getD 2026
  let mut rng := Rng.ofSeed seed
  let mut failures := 0
  let mut sat := 0
  let mut unsat := 0
  for idx in [0:cases] do
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
    let tmp := "execdiff_tmp.cnf"
    IO.FS.writeFile tmp cnf
    let solver ← AbsSat.Utils.ExhaustiveSolver.new tmp
    AbsSat.Utils.ExhaustiveSolver.run! solver
    let oracle ← solver.listSolutions.get
    let oracle_keys := keys_of (oracle.toList.map id)
    let gmap ← AbsSat.GraphMap.ImportCnf.load_import! tmp
    let machine ← AbsSat.SatMachine.new gmap
    AbsSat.SatMachine.run! machine
    let msat ← AbsSat.SatMachine.have_solution machine
    let ok ← if msat != !oracle.isEmpty then pure false
      else if !msat then pure true
      else match ← machine_solution_keys machine with
        | .error _ => pure false
        | .ok keys => pure ((set_diff oracle_keys keys).isEmpty && (set_diff keys oracle_keys).isEmpty)
    if ok then
      if msat then sat := sat + 1 else unsat := unsat + 1
    else
      failures := failures + 1
      IO.println s!"❌ case {idx} (vars={nVars}, clauses={nClauses}): machine={msat} oracle={!oracle.isEmpty}"
      IO.println cnf
  IO.println s!"exec-diff: {cases - failures}/{cases} agreed ({sat} SAT, {unsat} UNSAT), {failures} failures"
  return (if failures == 0 then 0 else 1)
