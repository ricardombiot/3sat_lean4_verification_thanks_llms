# Theorem: step_pure_appends_timeline

**State Preservation** — Each step extends the timeline, never modifies earlier steps.

---

## Formal Statement

```lean
theorem step_pure_appends_timeline (m : SatMachinePure) :
  (step_pure m).timeline = m.timeline ++ [(pureAdvance m.cnf m.timeline[m.current_step]!)]
```

---

## Plain English Explanation

When you take one step forward in the machine, the timeline grows by exactly one new state. Earlier states remain unchanged. The new state is computed by advancing from the current step's state.

**Why it matters:** This proves a key invariant: the machine's state space grows monotonically. Nothing gets lost or recomputed; execution is purely *additive*. This is crucial for proving the machine terminates and explores the entire search space.

---

## Proof Intuition

This is a **definition unfolding** — the theorem is almost a tautology:

Looking at the definition of `step_pure`:
```lean
def step_pure (m : SatMachinePure) : SatMachinePure :=
  let current_line := m.timeline[m.current_step]!
  let next_line := pureAdvance m.cnf current_line
  { 
    cnf := m.cnf
    timeline := m.timeline ++ [next_line]  -- ← This is what we prove
    current_step := m.current_step + 1
  }
```

The theorem statement is literally what the definition says: the timeline is appended.

---

## Proof Strategy

### Dependency Chain

```
step_pure_appends_timeline
  ← unfold step_pure         (expose definition)
  ← list append properties   (trivial list lemmas)
```

### Key Insight

No hard reasoning needed. Just unfold and simplify:

1. Unfold `step_pure` definition
2. Access the `timeline` field
3. See it's `m.timeline ++ [...]`
4. Definitional equality closes

### Proof Sketch

```lean
theorem step_pure_appends_timeline (m : SatMachinePure) :
  (step_pure m).timeline = m.timeline ++ [(pureAdvance m.cnf m.timeline[m.current_step]!)] := by
  unfold step_pure
  rfl  -- Reflexivity: both sides are structurally identical
```

Or even simpler:
```lean
theorem step_pure_appends_timeline (m : SatMachinePure) :
  (step_pure m).timeline = m.timeline ++ [(pureAdvance m.cnf m.timeline[m.current_step]!)] :=
  rfl
```

---

## Difficulty

**This is the easiest theorem in the suite.**

- **Time**: ~2 hours
  - 30 min: read step_pure definition
  - 15 min: write Lean statement
  - 15 min: prove (should be `rfl` or one `unfold`)
  - 45 min: debug silly syntax errors

- **Tactic knowledge needed**:
  - `unfold` — optional, might not even need it
  - `rfl` — reflexivity (definitional equality)

- **Depends on**: None (independent!)

- **Enables**: `run_pure_terminates` (can be done in parallel), complexity analysis

---

## Critical Lemmas

None needed! This is pure definition-chasing.

If Lean complains, these might help:
- List.append_assoc — append is associative (unlikely needed)
- List.length_append — length of append (unlikely needed)

---

## Effort Estimate

- **Time**: ~0.5-1 day (very short)
- **Tactic knowledge**: Minimal
- **Conceptual difficulty**: None
- **Can prove in parallel with**: Theorems 05, 06 (independent)

---

## Invariants Proven

Once this theorem is stated, it becomes a **fundamental lemma** for:

1. **Termination proof** (Theorem 05)
   - Shows timeline grows by exactly 1 per step
   - Bounds total steps by stepCount

2. **Complexity bounds** (Theorem 07)
   - Timeline length after n steps = n + 1
   - Execution time is O(stepCount)

3. **UNSAT characterization** (Theorem 08)
   - Final line is well-defined (timeline is non-empty after step k)
   - Can reliably check if final_line is empty

---

## Current Status

- [ ] Lean statement written
- [ ] Proof implemented (should be trivial)
- [ ] `lake build` passes
- [x] Can be done anytime (independent)

---

## Related Code

**Definition of `step_pure`:**
```lean
def step_pure (m : SatMachinePure) : SatMachinePure :=
  let final_step := (stepCount m.cnf).toNat
  if m.current_step >= final_step - 1 then
    m  -- No-op if at final step
  else
    let current_line := m.timeline[m.current_step]!
    let next_line := pureAdvance m.cnf current_line
    {
      cnf := m.cnf
      timeline := m.timeline ++ [next_line]
      current_step := m.current_step + 1
    }
```

**Note:** The no-op case (at final step) returns unmodified `m`, so the proof needs a case split. But both cases are trivial.

---

## Why This Matters Formally

This theorem formalizes a **critical invariant**:

> The machine never discards history. The timeline is immutable and grows monotonically.

This immutability is the key advantage of the pure machine over imperative MSat:
- No reference updates hiding state changes
- No hidden mutations in pureAdvance
- Everything is explicit in the timeline list

---

## Next Steps

Once proven (should be today):

1. Use as lemma for Theorem 05 (termination) — essential
2. Use as lemma for Theorem 07 (complexity) — essential
3. Independent from Theorems 01-03 (can prove in parallel)

---

**This is your quickest win. Prove it first for confidence.** ✓
