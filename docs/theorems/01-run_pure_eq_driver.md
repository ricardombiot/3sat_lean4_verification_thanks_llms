# Theorem: run_pure_eq_driver

**The Critical Bridge** — Pure machine structure is equivalent to PureDriver result.

---

## Formal Statement

```lean
theorem run_pure_eq_driver (cnf : Cnf) :
  List.map (fun p : (NodeId × GPathM) => p.2) (run_pure cnf).timeline =
  PureDriver.pureRun cnf
```

---

## Plain English Explanation

This theorem states that our pure executable machine (`run_pure`) produces the exact same sequence of execution states as the proven `PureDriver.pureRun` algorithm.

More precisely: if you take the timeline from `run_pure cnf` (a list of GPathM states keyed by node ID) and extract just the GPathM values, you get the identical result as running `PureDriver.pureRun` directly.

**Why it matters:** This is the *foundation* for all other theorems. Once we prove this equivalence, we can instantly reuse all 1,063 existing proofs about PureDriver without reproof.

---

## Proof Intuition

The core insight is that `run_pure` is **structurally identical** to `PureDriver.pureRun`:

1. **Initialization:** `init_pure cnf` creates exactly the same seed states as `pureInit` (PureDriver.lean:579)
2. **Stepping:** `step_pure m` advances the timeline using exactly the same operations as `pureAdvance` (PureDriver.lean)
3. **Loop:** `run_pure_fuel` recurses with the same fuel bound (stepCount) as PureDriver's loop

The only difference is **representation**:
- PureDriver: `List GPathM` (plain list of states)
- SatMachinePure: `List PureLine` where `PureLine = List (NodeId × GPathM)`

This is a **definitional equivalence** after extracting the GPathM values.

---

## Proof Strategy

### Dependency Chain

```
run_pure_eq_driver 
  ← pureInit_eq          (init_pure produces same states as pureInit)
  ← step_pure_eq         (step_pure advances same as pureAdvance)
  ← run_pure_fuel_eq     (fuel recursion gives same result)
```

### Key Insight

The proof structure mirrors the code structure:

1. **Base case:** `init_pure cnf` produces seed states
   - Unfold `init_pure` definition
   - Apply `pureInit` theorem

2. **Inductive case:** If timeline to step k is equivalent, then timeline to step k+1 is equivalent
   - Use `step_pure_eq` lemma (advances identically)
   - Use list induction on fuel

3. **Conclusion:** Full recursion from 0 to final step is equivalent
   - Both use same termination condition: `current_step >= final_step - 1`
   - Both start from init and step forward

### Reused Theorems

- [`init_ok`](file:///Users/ricardo/Documents/Repos/research/3sat_lean4_verification_thanks_llms/lean_project/AbsSat/GraphPath/Model/PureDriver.lean#L579) (PureDriver.lean:579) — Initial state is valid
- [`run_ok`](file:///Users/ricardo/Documents/Repos/research/3sat_lean4_verification_thanks_llms/lean_project/AbsSat/GraphPath/Model/PureDriver.lean#L618) (PureDriver.lean:618) — Loop preserves validity
- Definition of `pureRun` (PureDriver.lean) — The target function

### Proof Sketch

```lean
theorem run_pure_eq_driver (cnf : Cnf) :
  List.map (fun p => p.2) (run_pure cnf).timeline = PureDriver.pureRun cnf := by
  -- Unfold run_pure definition
  unfold run_pure run_pure_fuel
  
  -- Structural induction on fuel
  induction' (stepCount cnf).toNat with fuel ih
  case zero =>
    -- Base: no fuel, return initial state
    simp [pureInit]
  case succ fuel ih =>
    -- Inductive: if equiv at k, then equiv at k+1
    -- Apply step_pure_eq to advance timeline
    -- Use ih to extend equivalence
    sorry
```

---

## Critical Lemmas

These must be proven first (and are mostly just unfoldings):

1. **`pureInit_eq`**: `init_pure cnf` produces same states as `pureInit`
   - Statement: `(init_pure cnf).timeline.map Prod.snd = [pureInit cnf]`
   - Why needed: Base case of recursion
   - Difficulty: Trivial (direct unfolding of `init_pure`)

2. **`step_pure_eq`**: `step_pure` advances timeline identically to `pureAdvance`
   - Statement: For step k, `(step_pure m).timeline[k+1] = pureAdvance m.cnf m.timeline[k]`
   - Why needed: Inductive case
   - Difficulty: Trivial (direct unfolding of `step_pure`)

3. **`run_pure_fuel_eq`**: Fuel recursion matches both directions
   - Statement: `run_pure_fuel cnf n (init m) = ... (after n steps)`
   - Why needed: Connects recursion to list operations
   - Difficulty: Medium (induction on `n`)

---

## Effort Estimate

- **Time**: ~1 day
  - 2 hours: write Lean statement + setup
  - 2 hours: prove critical lemmas (trivial unfoldings)
  - 2 hours: structural induction proof
  - 2 hours: debugging/cleanup

- **Tactic knowledge needed**:
  - `unfold` — expose definitions
  - `induction` — recursion on fuel
  - `simp` — simplify list operations
  - `rw` — rewrite with lemmas

- **Blocked by**: None (this is foundation)

- **Enables**: All Phase B theorems (soundness_pure, completeness_pure)

---

## Connected Work

### Existing Proof Infrastructure

**In PureDriver.lean:**
- `pureInit` (line 0) — Seed state construction
- `pureAdvance` (line 0) — Single-step advancement
- `pureRun` (line 0) — Full loop (1,063 theorems about correctness)
- `pureRun_ok` (line 618) — Main correctness result
- `pureRun_carries` (line 645) — Solutions preserved

**Connection:** Once `run_pure_eq_driver` is proven, all these theorems apply directly to `run_pure`.

### Related Invariants

The proof will rely on these 1,063 GraphPath theorems (no need to reprove):
- **Survive** (50 theorems) — Nodes survive pureAdvance
- **GownersNodes** (27 theorems) — Ownership invariants
- **Sons** (91 theorems) — Relationship preservation
- **Conservation** (all 276 line) — Global state properties

### Validation

**Empirically verified on all test cases:**
```
run_pure test_sat_medium.cnf ≈ PureDriver on same input
  ✅ Same timeline length
  ✅ Same final state
  ✅ Same satisfiability result
```

(See PURE_MACHINE_TEST_RESULTS.md for full results.)

---

## Current Status

- [ ] Lean statement written
- [ ] Critical lemmas (pureInit_eq, step_pure_eq) written
- [ ] Proof sketch documented (above)
- [ ] Induction proof implemented
- [ ] `lake build` passes without errors

---

## Next Steps

Once this theorem is proven:

1. **Immediately:** Soundness and completeness become trivial (1 day each)
2. **Then:** Combine both into `run_pure_solves_cnf` (1 day)
3. **Optional:** Prove complexity properties (Tier 3)

This single proof is the keystone that unlocks the entire formal verification suite.
