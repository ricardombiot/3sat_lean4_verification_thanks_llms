# Theorem: run_pure_terminates

**Guaranteed Termination** — The machine always completes in finite time.

---

## Formal Statement

```lean
theorem run_pure_terminates (cnf : Cnf) :
  ∃ m : SatMachinePure, run_pure cnf = m
```

---

## Plain English Explanation

No matter what CNF formula you give it, `run_pure` will finish executing and return a complete result. The machine doesn't hang, loop infinitely, or require unbounded computation.

**Why it matters:** This is a *liveness* property. Soundness and completeness are *correctness* properties (is the answer right?). Termination is a *guarantee* that you'll ever get an answer at all.

---

## Proof Intuition

The proof is straightforward because `run_pure` uses **fuel**:

```lean
def run_pure (cnf : Cnf) : SatMachinePure :=
  let final_step := (stepCount cnf).toNat
  run_pure_fuel cnf final_step (init_pure cnf)
```

The fuel is `stepCount cnf` — a *finite bound* on the number of steps. Since fuel is finite and decreases by 1 each recursion, the function must terminate.

**Key insight:** `stepCount` is computed from the CNF structure, so it's always a concrete number. Lean's termination checker accepts this readily.

---

## Proof Strategy

### Dependency Chain

```
run_pure_terminates
  ← run_pure_fuel_terminates   (fuel recursion is trivially finite)
  ← Nat.recOn termination     (recursion on natural numbers terminates)
  ← stepCount bounds          (output of stepCount is always a Nat)
```

### Key Insight

Fuel-based recursion terminates by structural induction:

1. Base case: `fuel = 0` — return immediately
2. Inductive case: `fuel = n+1` — recurse on smaller `n`
3. By Nat.recOn principle, this terminates

### Proof Sketch

```lean
theorem run_pure_terminates (cnf : Cnf) :
  ∃ m : SatMachinePure, run_pure cnf = m := by
  -- Unfold run_pure and run_pure_fuel
  unfold run_pure run_pure_fuel
  
  -- The result is defined by fuel recursion
  -- Lean's built-in termination checker should accept this
  
  -- If not, provide explicit witness
  use (run_pure_fuel cnf (stepCount cnf).toNat (init_pure cnf))
  -- Lean knows this value exists because run_pure_fuel is total
```

Or even simpler — just note that `run_pure` is defined:
```lean
theorem run_pure_terminates (cnf : Cnf) : ∃ m, run_pure cnf = m :=
  ⟨run_pure cnf, rfl⟩
```

This works because if `run_pure` reduces to a value, that value exists.

---

## Critical Lemmas

These are mostly infrastructure that Lean already knows:

1. **`run_pure_fuel_terminates`**: Fuel recursion is total
   - Statement: `∀ cnf fuel init, ∃ m, run_pure_fuel cnf fuel init = m`
   - Why needed: Reduce to fuel property
   - Difficulty: Trivial (Lean's termination checker)

2. **`stepCount_is_nat`** (EXISTING): `stepCount cnf : ℕ`
   - Already proven in CnfMap.lean
   - Why needed: Proves fuel is finite
   - No reproof needed

3. **Nat.rec termination** (EXISTING): Lean built-in
   - Recursion on `n : ℕ` is total
   - Lean knows this automatically

---

## Effort Estimate

- **Time**: ~0.5-1 day
  - 1 hour: understand fuel-based definition
  - 30 min: write Lean statement
  - 30 min: provide witness or apply termination checker
  - 30 min: debug/verify

- **Tactic knowledge needed**:
  - `unfold` — expose definitions
  - `use` — provide witness
  - `rfl` — reflexivity
  - Trust termination checker (mostly automatic)

- **Depends on**: None (independent!)

- **Enables**: Theorem 07 (complexity bounds)

---

## Why This Is Not Hard

The machine terminates because:

1. **Fuel is finite:** `stepCount cnf` outputs a concrete `ℕ`
2. **Fuel decreases:** Each recursive call uses `fuel - 1`
3. **Decreasing function:** Recursion on smaller fuel always terminates

Lean's termination checker automatically verifies this pattern.

---

## Related Theorems

**Step preservation** (Theorem 04) supports this:
- Each `step_pure` call extends timeline by 1
- Timeline length after n steps = n + 1
- When timeline length = stepCount, we stop
- Therefore, exactly stepCount steps occur

This makes the termination argument crystal clear:
> Bounded by stepCount + 1 steps → Must terminate

---

## Current Status

- [ ] Lean statement written
- [ ] Proof implemented (should be nearly automatic)
- [ ] `lake build` passes
- [x] Can be done anytime (independent)

---

## Variants (in order of preference)

### Option 1: Trivial (Just Provide Witness)
```lean
theorem run_pure_terminates (cnf : Cnf) : ∃ m, run_pure cnf = m :=
  ⟨run_pure cnf, rfl⟩
```
Lean automatically handles termination for `run_pure` since it's defined.

### Option 2: Fuel-Based (Explicit Recursion)
```lean
theorem run_pure_fuel_terminates (cnf : Cnf) (fuel : ℕ) (init : SatMachinePure) :
  ∃ m, run_pure_fuel cnf fuel init = m := by
  cases fuel with
  | zero => exact ⟨init, rfl⟩
  | succ n => 
    -- Recursive case: call hypothesis
    have := run_pure_fuel_terminates cnf n (step_pure init)
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm⟩
```

### Option 3: Using Well-Founded (Advanced)
Define a measure that decreases with each step and use well-founded recursion. (Overkill for this problem.)

---

## Why Termination Matters

Termination is **non-trivial for SAT solvers** in general:
- Backtracking algorithms can have pathological cases
- Search trees can be exponential
- Without careful design, solvers can timeout

But for **this machine**:
- Steps are bounded by CNF structure
- No heuristics or randomness that could cause looping
- Formula size is input-bounded
- Termination is **by construction**

---

## Next Steps

Once proven (should be same day):

1. Use for Theorem 07 (complexity bounds)
2. Combine with step preservation (Theorem 04) for full timing analysis

This is your second quickest proof. ✓
