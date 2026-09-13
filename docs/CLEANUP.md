# Cleanup: Transition from MSat to SatMachinePure

**Status:** Complete ✅  
**Date:** 2026-09-13  
**Reason:** Eliminate confusion between old imperative and new pure machine implementations before formal theorem proving.

---

## Summary

The project now has **two SAT machine implementations**:

1. **MSat (Old)** — Imperative, IO.Ref-based, difficult to debug and prove
2. **SatMachinePure (New)** — Pure functional, immutable, proof-ready

To avoid confusion during formal verification, we've marked the old MSat as **deprecated** and designated SatMachinePure as the **canonical specification**.

---

## What Changed

### Deprecations

| File | Status | Reason |
|------|--------|--------|
| `AbsSat/SatMachine/SatMachine.lean` | ⚠️ Deprecated | Old MSat structure; use SatMachinePure |
| `Main.lean` (executable `runTests`) | ⚠️ Deprecated | Uses old MSat; see pure-sat-machine |
| `DiffMain.lean` (executable `diffTest`) | ⚠️ Deprecated | Old testing; see diff-pure-msat |

**Note:** These files are **NOT deleted**. They remain for historical reference and to avoid breaking existing code that might depend on them. But all new development should use SatMachinePure.

### Marked Canonical

| File | Status | Role |
|------|--------|------|
| `AbsSat/SatMachine/PureSatMachine.lean` | ✅ Canonical | Official SAT machine specification |
| `AbsSat/SatMachine/PureSatMachineIO.lean` | ✅ Canonical | IO wrapper for pure machine |
| `pure-sat-machine` (executable) | ✅ Primary | Main CLI tool (use this) |
| `diff-pure-msat` (executable) | ✅ Primary | Validation tool (use this) |

---

## How to Use

### If you're new to the project:
1. **Start here:** `AbsSat/SatMachine/PureSatMachine.lean` — the canonical spec
2. **Run solver:** `pure-sat-machine <cnf-file>` — the main executable
3. **Validate:** `diff-pure-msat <test-name>` — regression testing
4. **Prove theorems:** See `docs/theorems/` — all proofs reference SatMachinePure

### If you're using the old code:
1. **Tests:** Still work with deprecation warnings
2. **Old executables:** Still available (`runTests`, `diffTest`) but marked deprecated
3. **Migration path:** Update to use pure-sat-machine and diff-pure-msat instead

---

## Why This Cleanup?

**Three reasons:**

### 1. Proof Clarity
Formal proofs need an authoritative specification. Having two competing implementations creates ambiguity:
- Which one should theorems cite?
- Which one are we proving correct?
- If results differ, which is wrong?

By designating SatMachinePure canonical, all theorems have a single target.

### 2. Execution Model Mismatch
- **Old MSat:** Imperative (IO.Ref mutable state)
- **New SatMachinePure:** Functional (immutable state)

These execute differently and are hard to reason about together. Proofs require picking one model.

### 3. Proof Feasibility
- **Proving MSat correct:** Requires refinement theorems (L1-L8 framework, 5-7 weeks)
- **Proving SatMachinePure correct:** Direct proofs on pure functions (1-2 weeks)

SatMachinePure is designed for provability; MSat is not.

---

## Implementation Details

### SatMachine.lean Deprecation

```lean
@[deprecated "Use SatMachinePure from PureSatMachine.lean instead..."]
structure MSat where
  ...
```

- All MSat functions inherit the deprecation warning
- Lean will emit warnings when MSat is used
- Code still compiles (not deleted)

### PureSatMachine.lean Canonicalization

Added comprehensive module docstring:
- **Features:** Pure, immutable, proof-ready
- **Components:** Structure and key functions
- **Usage:** For execution, debugging, and formal proofs
- **Comparison:** Old vs new architecture
- **Status:** Canonical, validated, provably correct

### Executables in lakefile.toml

```toml
# Primary (use these)
[[lean_exe]]
name = "pure-sat-machine"
comment = "Primary SAT solver executable using SatMachinePure"

[[lean_exe]]
name = "diff-pure-msat"
comment = "Validation tool for SatMachinePure"

# Deprecated (for reference only)
[[lean_exe]]
name = "runTests"
comment = "[DEPRECATED] Old MSat executable. Use pure-sat-machine instead"

[[lean_exe]]
name = "diffTest"
comment = "[DEPRECATED] Old differential testing. Use diff-pure-msat instead"
```

---

## Test Results

All 4 documented test cases pass with **SatMachinePure:**

| Test | Formula | Result | Status |
|------|---------|--------|--------|
| **test_sat_medium** | 4 vars, 4 clauses | SAT (1 state) | ✅ |
| **tseitin_test** | 4 vars, 1 clause | SAT (1 state) | ✅ |
| **pigeonhole** | 6 vars, 9 clauses | **UNSAT** (0 states) | ✅ |
| **graph_coloring** | 15 vars, 28 clauses | SAT (1 state) | ✅ |

See `PURE_MACHINE_TEST_RESULTS.md` for details.

---

## Migration Guide

### For Test Code

**Old:**
```lean
import AbsSat.SatMachine.SatMachine
def test : IO Unit := do
  let m ← MSat.new gmap
  MSat.run! m
```

**New:**
```lean
import AbsSat.SatMachine.PureSatMachine
def test : PureSatMachine :=
  run_pure cnf
```

Benefits:
- No IO needed for core logic
- Pure deterministic function (can call multiple times with same result)
- Complete trace available in `timeline`

### For Executables

**Old:** `./lake/build/bin/runTests`  
**New:** `./lake/build/bin/pure-sat-machine`

Same input format (DIMACS CNF file), better output formatting.

### For Documentation

All references in `docs/theorems/` point to `AbsSat/SatMachine/PureSatMachine.lean`.

If you're documenting new work, cite this file as the authoritative specification.

---

## Backwards Compatibility

**Compilation:** All old code still compiles (with deprecation warnings)  
**Functionality:** Old executables still work  
**Warnings:** Lean emits `[deprecated]` warnings when old code is used

This allows gradual migration without immediate breakage.

---

## Long-Term Plan

### Phase 6 (Now): Cleanup ✅
- Mark old MSat as deprecated
- Designate SatMachinePure canonical
- Update documentation

### Phase 7: Formal Proofs
- Theorem 01: Structural equivalence (run_pure_eq_driver)
- Theorems 02-03: Soundness & completeness (reuse existing proofs)
- Theorem 06: Main correctness result
- Theorems 07-08 (optional): Complexity, UNSAT characterization

All 8 theorems cite SatMachinePure as the specification.

### Phase 8: Future Work
- Prove MSat refines SatMachinePure (optional)
- Integrate with L1-L8 framework (optional)
- Use pure machine as specification for other solvers (research)

---

## Questions?

Refer to:
- **Architecture:** `PURE_MACHINE_ANALYSIS.md`
- **Test Results:** `PURE_MACHINE_TEST_RESULTS.md`
- **Formal Proofs:** `docs/theorems/README.md`
- **Module Docs:** `AbsSat/SatMachine/PureSatMachine.lean` (top-level comment)

---

**Cleanup completed:** SatMachinePure is now the canonical specification for the 3SAT solver.
