# Validation Tools

Brute-force validators that prove Reader correctness by comparing against ground truth.

## How They Work

Each validator:
1. Generates all 2^n possible variable assignments
2. Evaluates the formula on each assignment (ground truth)
3. Runs the Reader to extract solutions
4. Compares Reader output against ground truth
5. Reports: correctness, completeness, and match status

## Executables

### ValidateTseitin
Validates Reader on Tseitin encoding.

```
Build:  lake build tseitin-validate
Run:    ./.lake/build/bin/tseitin-validate
Input:  tseitin_test.cnf (4 vars, 5 clauses)
Output: 32 solutions (brute force) vs Reader extraction
Result: ✅ PERFECT MATCH
```

### ValidatePigeonhole
Validates Reader on Pigeonhole formula (UNSAT case).

```
Build:  lake build pigeonhole-validate
Run:    ./.lake/build/bin/pigeonhole-validate
Input:  pigeonhole.cnf (6 vars, 9 clauses)
Output: 0 solutions (UNSAT)
Result: ✅ PERFECT MATCH
Note:   Tests unsatisfiable formula handling
```

### ValidateGraphColoring
Validates Reader on graph coloring problem.

```
Build:  lake build graph-coloring-validate
Run:    ./.lake/build/bin/graph-coloring-validate
Input:  graph_coloring_3col.cnf (15 vars, 28 clauses)
Output: 12 valid colorings (out of 32,768 possible)
Result: ✅ PERFECT MATCH
Note:   Most complex test case (largest problem)
```

## Validation Framework Benefits

✅ **Correctness Proof:** Brute-force enumeration = definitive ground truth  
✅ **Completeness Verification:** Ensures no solutions are missed  
✅ **CNF Bug Detection:** Catches parser errors immediately  
✅ **Scalability Testing:** Works up to ~20 variables  
✅ **Problem Coverage:** Tests SAT, UNSAT, and mixed clause sizes  

## Test Results Summary

| Validator | Variables | Solutions | Brute Force | Reader | Status |
|-----------|-----------|-----------|------------|--------|--------|
| Tseitin | 4 | 32 | ✅ | ✅ | PASS |
| Pigeonhole | 6 | 0 (UNSAT) | ✅ | ✅ | PASS |
| GraphColoring | 15 | 12 | ✅ | ✅ | PASS |

## Requirements

- Lean 4 with Lake build tool
- CNF test files in appropriate locations (see `lean_project/test/cnf/`)
- ~2-5 seconds execution time per validator

## See Also

- [`../index.md`](../index.md) — All executables index
- [`../../test/cnf/README.md`](../../test/cnf/README.md) — CNF test files
- [`../../../docs/analysis/validation-reports/`](../../../docs/analysis/validation-reports/) — Detailed validation reports

---

*Last updated: 2026-09-13*
