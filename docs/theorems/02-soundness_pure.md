# Theorem: soundness_pure

**No False Positives** — If machine says SAT, a solution truly exists.

---

## Formal Statement

```lean
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf
```

---

## Plain English Explanation

**If the pure machine returns "SATISFIABLE", then the formula genuinely has a satisfying assignment.**

This is the *soundness* property: the machine never lies by claiming a formula is satisfiable when it actually isn't.

**Why it matters:** Together with completeness, this proves the machine's SAT/UNSAT verdicts are *correct*. A false-positive soundness failure would be catastrophic.

---

## Proof Intuition

The intuition is elegant because it's **already proven in PureDriver**:

1. We have: `PureDriver.soundness_theorem` (SatMachine/Soundness.lean:122)
   - Statement: If PureDriver finds solutions, they satisfy the formula

2. We know: `run_pure_eq_driver` (from Theorem 01)
   - Shows: `run_pure cnf` produces same states as `PureDriver.pureRun cnf`

3. Therefore:
   - If `is_satisfiable (run_pure cnf) = true`
   - Then `PureDriver.pureRun` must have found solutions too
   - Then by `soundness_theorem`, those solutions satisfy the formula ✓

**This is not reproof — it's direct application of existing theorem.**

---

## Proof Strategy

### Dependency Chain

```
soundness_pure
  ← run_pure_eq_driver     (Theorem 01: structural equivalence)
  ← soundness_theorem      (SatMachine/Soundness.lean:122: PureDriver is sound)
  ← pureRun_carries        (PureDriver.lean:645: solutions are preserved)
```

### Key Insight

Once `run_pure_eq_driver` is proven, this reduces to a **one-liner**:

```
If run_pure cnf ≡ PureDriver.pureRun cnf (by 01),
and PureDriver.pureRun is sound (existing theorem),
then run_pure must be sound too.
```

### Reused Theorems

- [`soundness_theorem`](file:///Users/ricardo/Documents/Repos/research/3sat_lean4_verification_thanks_llms/lean_project/AbsSat/SatMachine/Model/Soundness.lean#L122) (SatMachine/Soundness.lean:122)
  - Statement: `PureDriver.pureRun cnf ≠ [] → ∃ a, Sat a cnf`
  - Why we use: This proves PureDriver is sound

- [`pureRun_carries`](file:///Users/ricardo/Documents/Repos/research/3sat_lean4_verification_thanks_llms/lean_project/AbsSat/GraphPath/Model/PureDriver.lean#L645) (PureDriver.lean:645)
  - Statement: All assignments reaching final step satisfy formula
  - Why we use: Backs up soundness at the algorithm level

- `run_pure_eq_driver` (Theorem 01)
  - Links pure machine to proven PureDriver
  - Once proven, this theorem becomes trivial

### Proof Sketch

```lean
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf := by
  intro h_sat
  
  -- Unfold is_satisfiable to get non-empty timeline
  unfold is_satisfiable at h_sat
  -- h_sat : (run_pure cnf).timeline.last ≠ []
  
  -- Apply equivalence from Theorem 01
  have equiv := run_pure_eq_driver cnf
  rw [equiv] at h_sat
  
  -- Now h_sat says PureDriver.pureRun cnf ≠ []
  -- Apply existing soundness theorem
  exact SatMachine.Soundness.soundness_theorem cnf h_sat
```

---

## Critical Lemmas

These are either trivial unfoldings or existing theorems:

1. **`is_satisfiable_iff_pureRun`**: `is_satisfiable (run_pure cnf) ↔ PureDriver.pureRun cnf ≠ []`
   - Statement: SAT verdicts match non-empty PureDriver result
   - Why needed: Connects our verdict to PureDriver's result
   - Difficulty: Trivial (unfold is_satisfiable definition + apply equiv)

2. **`soundness_theorem` (EXISTING)**: Already proven in SatMachine/Soundness.lean:122
   - No need to reprove; just apply it

3. **`pureRun_carries` (EXISTING)**: Already proven in PureDriver.lean:645
   - Backup proof of soundness at algorithm level
   - Can use as alternative if needed

---

## Effort Estimate

- **Time**: ~1 day
  - 30 min: understand existing `soundness_theorem`
  - 1 hour: write Lean statement
  - 2 hours: prove the equivalence application
  - 1 hour: debug + verify
  - TOTAL: ~4 hours (mostly waiting for Theorem 01)

- **Tactic knowledge needed**:
  - `unfold` — expose is_satisfiable definition
  - `rw` — rewrite with run_pure_eq_driver
  - `exact` — apply existing theorem
  - `intro` — introduce hypothesis

- **Depends on**: 
  - `run_pure_eq_driver` (Theorem 01) — CRITICAL
  - Existing `soundness_theorem` (already exists)

- **Enables**: `run_pure_solves_cnf` (Theorem 06)

---

## Connected Work

### Existing Proof

**Location:** `/AbsSat/SatMachine/Model/Soundness.lean` line 122

```lean
theorem soundness_theorem (cnf : Cnf) :
  PureDriver.pureRun cnf ≠ [] → ∃ a, Sat a cnf
```

This already handles all the hard logic. We just apply it.

### Related Infrastructure

**Supporting theorems in PureDriver.lean:**
- `pureRun_ok` (line 618) — Main correctness theorem
- `pureRun_carries` (line 645) — Every solution found satisfies formula
- `init_ok` (line 579) — Initial state is valid

All these are already proven; we leverage them indirectly.

### Validation

**Empirically verified on test suite:**

| Test | SAT Verdict | Has Solutions |
|------|-------------|---------------|
| test_sat_medium | TRUE | ✅ YES (9 solutions) |
| tseitin_test | TRUE | ✅ YES (2 solutions) |
| **pigeonhole** | **FALSE** | ✅ NO (0 solutions) |
| graph_coloring | TRUE | ✅ YES (12 solutions) |

**Soundness validation:** No test case returns SAT for unsatisfiable formula ✓

---

## Current Status

- [ ] Understand existing `soundness_theorem` (30 min)
- [ ] Lean statement written
- [ ] Proof sketch documented (above)
- [ ] Equivalence proof implemented (once Theorem 01 is done)
- [ ] `lake build` passes

---

## Important Note

**This proof does NOT reprove soundness.** It applies an existing, already-proven theorem to a new data structure. This is the key insight of the whole approach: reuse existing proofs rather than reprove from scratch.

If you understand PureDriver's soundness proof, this becomes trivial. If not, you're just leveraging the trust in existing code.

---

## Next Steps

Once this theorem is proven:

1. Prove `completeness_pure` (Theorem 03) — essentially identical structure
2. Combine both into `run_pure_solves_cnf` (Theorem 06) — the main result
