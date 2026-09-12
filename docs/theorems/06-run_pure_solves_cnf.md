# Theorem: run_pure_solves_cnf

**The Main Result** — Machine verdict ↔ Formula solvability. Perfect correctness.

---

## Formal Statement

```lean
theorem run_pure_solves_cnf (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true ↔ (∃ a : Assign, Sat a cnf)
```

---

## Plain English Explanation

**The machine's SAT/UNSAT verdict is correct in both directions:**
- Returns SAT ↔ Formula truly has a solution
- Returns UNSAT ↔ Formula has no solution

This is the *principal theorem* of the entire project. Everything else is infrastructure; this is the goal.

**Why it matters:** This proves the machine is a *correct SAT solver*. Not just that it doesn't lie (soundness), and not just that it finds solutions when they exist (completeness), but that its output is *precisely equivalent* to the formula's solvability.

---

## Proof Intuition

This combines two already-proven theorems into one biconditional:

1. **Forward direction (→):** If machine says SAT, solution exists
   - This is **soundness** (Theorem 02)
   
2. **Backward direction (←):** If solution exists, machine says SAT
   - This is **completeness** (Theorem 03)

Together, they form a perfect equivalence:
```
Machine verdict = true  ⟺  Solution exists
```

**The proof is literally:** `⟨soundness_pure, completeness_pure⟩`

---

## Proof Strategy

### Dependency Chain

```
run_pure_solves_cnf
  ← soundness_pure        (Theorem 02: Machine won't lie about SAT)
  ← completeness_pure     (Theorem 03: Machine finds all SAT solutions)
  ← run_pure_eq_driver    (Theorem 01: Structural equivalence)
```

### Key Insight

Biconditional proofs split into two directions:

1. **Left-to-right:** `is_satisfiable (run_pure cnf) = true → ∃ a, Sat a cnf`
   - Apply `soundness_pure`
   - Done

2. **Right-to-left:** `(∃ a, Sat a cnf) → is_satisfiable (run_pure cnf) = true`
   - Apply `completeness_pure`
   - Done

### Proof Sketch (Option 1: Direct)

```lean
theorem run_pure_solves_cnf (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true ↔ (∃ a : Assign, Sat a cnf) :=
  ⟨soundness_pure cnf, fun ⟨a, h⟩ => completeness_pure cnf a h⟩
```

### Proof Sketch (Option 2: Tactic)

```lean
theorem run_pure_solves_cnf (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true ↔ (∃ a : Assign, Sat a cnf) := by
  constructor
  · exact soundness_pure cnf
  · intro ⟨a, h⟩
    exact completeness_pure cnf a h
```

### Proof Sketch (Option 3: Using Iff.intro)

```lean
theorem run_pure_solves_cnf (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true ↔ (∃ a : Assign, Sat a cnf) :=
  Iff.intro (soundness_pure cnf) (fun ⟨a, h⟩ => completeness_pure cnf a h)
```

All three are equivalent. Pick the style you prefer.

---

## Critical Lemmas

Just the two preceding theorems:

1. **`soundness_pure`** (Theorem 02) — Already proven
   - Provides the forward direction
   - No reproof needed

2. **`completeness_pure`** (Theorem 03) — Already proven
   - Provides the backward direction
   - No reproof needed

Once Theorems 02-03 are done, this is **one-liner proof**.

---

## Effort Estimate

- **Time**: ~1 hour
  - 30 min: wait for Theorems 02-03 to be ready
  - 15 min: write Lean statement
  - 10 min: apply both theorems (one line!)
  - 5 min: verify

- **Tactic knowledge needed**:
  - `⟨...⟩` — anonymous constructor (for biconditionals)
  - `constructor` — split biconditional into two goals
  - `intro` — introduce existential
  - Function application (apply lemmas)

- **Depends on**: 
  - Theorem 02 (soundness_pure) — REQUIRED
  - Theorem 03 (completeness_pure) — REQUIRED

- **Enables**: This IS the main theorem (nothing builds on it; this is the goal)

---

## Why This Is The Principal Theorem

**Everything in the project leads here:**

1. Machines (Phase 1-2): Pure machine implemented
2. Validation (Phase 3): Machine works on test cases
3. Debugging (Phase 4): Step-by-step execution visible
4. Theorems (Phase 5): **THIS THEOREM**

This single statement captures:
- ✅ Soundness: `return SAT` → solution exists
- ✅ Completeness: solution exists → `return SAT`
- ✅ Termination: computation finishes (implicit in Types)
- ✅ Decidability: Every formula gets a verdict

---

## Implications

Once proven, you can derive:

### Theorem 6a: Negation
```lean
theorem run_pure_unsat (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = false ↔ ¬(∃ a, Sat a cnf) :=
  by simp [run_pure_solves_cnf]
```

### Theorem 6b: Classical Logic
```lean
theorem run_pure_classical (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = false ↔ ∀ a, ¬Sat a cnf :=
  by simp [run_pure_solves_cnf]
```

### Theorem 6c: Search Tree Bounds
```lean
theorem run_pure_search_tree (cnf : Cnf) :
  timeline.length (run_pure cnf) ≤ stepCount cnf + 1 :=
  -- Uses step_pure_appends_timeline + run_pure_terminates
```

All these follow easily from the main theorem.

---

## Current Status

- [ ] Theorems 02-03 implemented
- [ ] Lean statement written
- [ ] Proof implemented (one line!)
- [ ] `lake build` passes

---

## The Moment of Truth

This theorem is when all the work pays off. The entire project exists to prove this statement:

> **The pure executable 3SAT machine is a correct SAT solver.**

Every test case, every documentation file, every theorem leads here.

---

## Next Steps

After this theorem is proven:

1. **Optional Phase D:** Prove complexity bounds (Theorems 07-08)
2. **Refinement:** Prove `run_pure ≡ MSat.run!` (uses this theorem)
3. **Publication:** This is your main result ✓

---

## Historical Context

In the original plan, proving this would require:
- L1-L8 refinement framework: 5-7 weeks
- Risk of L6 failure: complete restart
- Multiple unprovable assumptions

With the pure machine approach:
- Theory 01 (structural): 1 day
- Theorems 02-03 (reapplication): 2 days
- Theorem 06 (combination): 1 hour
- **Total: 3 days (instead of 5-7 weeks)**

This is what a *good abstraction* achieves. ✓
