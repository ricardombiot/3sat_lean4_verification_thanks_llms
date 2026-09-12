# CNF Test Files

Collection of 3-SAT formulas in standard DIMACS CNF format for testing and validation.

## Directory Organization

### satisfiable/
Formulas with at least one satisfying assignment.

**simple/** — Basic test cases
- `test_sat_medium.cnf` (4 vars, 4 clauses, **9 solutions**)
  - Standard 3-literal clauses
  - Used for basic Reader functionality testing
  - Satisfiable: YES

- `simple_test.cnf`
  - Additional simple test case

**tseitin/** — Tseitin encoding variants
- `tseitin_test.cnf` (4 vars, 5-6 clauses, **32 solutions**)
  - Mixed 1-3 literal clauses
  - Tests auxiliary variable handling
  - Satisfiable: YES

- `tseitin_correct.cnf`
  - Corrected Tseitin transformation
  - Reference encoding variant

**graph-coloring/** — Combinatorial optimization
- `graph_coloring_3col.cnf` (15 vars, 28 clauses, **12 solutions**)
  - 5 vertices, 3 colors, 6 edges
  - Largest test case
  - Demonstrates scalability
  - Satisfiable: YES (valid 3-colorings exist)

### unsatisfiable/
Formulas with NO satisfying assignments.

**pigeonhole/** — Classic unsatisfiable problem
- `pigeonhole.cnf` (6 vars, 9 clauses, **0 solutions**)
  - Pigeonhole Principle: 3 pigeons in 2 holes
  - Tests UNSAT formula handling
  - Satisfiable: NO (by pigeonhole principle)

### development/
Temporary test files created during development.

- `test_2lit.cnf` — Tests 2-literal clause support
- `convergence_test.cnf` — Tests convergence behavior
- Files in this directory are NOT committed to version control

### reference/
External reference instances from other test suites.

- May contain larger instances for scalability testing
- Imported from `docs/original_julia/test/example_cnf/`

## Quick Reference

| Formula | Type | Vars | Clauses | Solutions | Status |
|---------|------|------|---------|-----------|--------|
| test_sat_medium | SAT | 4 | 4 | 9 | ✅ |
| tseitin_test | SAT | 4 | 5-6 | 32 | ✅ |
| graph_coloring_3col | SAT | 15 | 28 | 12 | ✅ |
| pigeonhole | UNSAT | 6 | 9 | 0 | ✅ |

## Using These Files

### For Reader Validation
```bash
cd ../../
lake build reader           # Build Reader on test_sat_medium
lake build tseitin          # Build Reader on tseitin
lake build pigeonhole-reader # Build Reader on pigeonhole
lake build graph-coloring-reader # Build Reader on graph coloring
```

### For Brute-Force Validation
```bash
lake build tseitin-validate
lake build pigeonhole-validate
lake build graph-coloring-validate
```

### Loading in Lean Programs
CNF files are loaded using:
```lean
let gmap ← AbsSat.GraphMap.ImportCnf.load_import! "path/to/formula.cnf"
```

## CNF Format

Standard DIMACS format:
- Comments: Lines starting with `c`
- Header: `p cnf <nvars> <nclauses>`
- Clauses: Space-separated literals, terminated with `0`
- Positive literal: variable number (1-indexed)
- Negative literal: `-<variable number>`

**Example:**
```
c Simple formula: (x1 ∨ x2) ∧ (¬x1 ∨ x2)
p cnf 2 2
1 2 0
-1 2 0
```

## Validation Results

All formulas have been validated using:
1. **Brute-force enumeration** (ground truth)
2. **Reader extraction** (algorithm under test)
3. **Solution verification** (correctness check)

**Status:** ✅ All formulas validated (PERFECT MATCH)

## Adding New Test Cases

To add a new CNF formula:
1. Create file in appropriate subdirectory
2. Ensure DIMACS format compliance
3. Create corresponding validator in `../../executables/validation-tools/`
4. Update this README with new formula details
5. Add to lakefile.toml if creating new validator

## Test Coverage

✅ **SAT formulas** (various sizes)  
✅ **UNSAT formulas** (pigeonhole principle)  
✅ **Tseitin encodings** (auxiliary variables)  
✅ **Mixed clause sizes** (2-3 literal clauses)  
✅ **Combinatorial problems** (graph coloring)  
✅ **Problem range** (4 to 15 variables)  

## See Also

- [`../executables/index.md`](../executables/index.md) — Executables that use these files
- [`../executables/validation-tools/README.md`](../executables/validation-tools/README.md) — Validation framework
- [`../../docs/analysis/validation-reports/`](../../docs/analysis/validation-reports/) — Validation results

---

*Last updated: 2026-09-13*
