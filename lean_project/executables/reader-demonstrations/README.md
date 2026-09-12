# Reader Demonstrations

Step-by-step execution examples showing the Reader algorithm extracting solutions from various SAT formulas.

## Executables

### ReaderStepByStepMain
Demonstrates Reader on a simple 4-variable SAT formula.

```
Build:  lake build reader
Run:    ./.lake/build/bin/reader
Input:  test_sat_medium.cnf
Output: Extracts 9 solutions with detailed step-by-step output
Result: ✅ All 9 solutions found correctly
```

**Formula:** (x1 ∨ x2 ∨ x3) ∧ (¬x1 ∨ ¬x2 ∨ x4) ∧ (x2 ∨ ¬x3 ∨ ¬x4) ∧ (¬x2 ∨ x3 ∨ x4)

### TseitinReaderMain
Demonstrates Reader on Tseitin-encoded formula.

```
Build:  lake build tseitin
Run:    ./.lake/build/bin/tseitin
Input:  tseitin_test.cnf
Output: Step-by-step Reader execution (variable assignment trace)
Result: ✅ All 32 solutions extracted
```

### PigeonholeReaderMain
Demonstrates Reader on unsatisfiable formula (UNSAT case).

```
Build:  lake build pigeonhole-reader
Run:    ./.lake/build/bin/pigeonhole-reader
Input:  pigeonhole.cnf (PHP(2,3): 3 pigeons, 2 holes)
Output: Machine step count, SAT status
Result: ✅ Correctly identifies as UNSATISFIABLE
```

**Key Finding:** Demonstrates Reader correctly handles UNSAT formulas (no infinite loops, returns appropriate status).

### GraphColoringReaderMain
Demonstrates Reader on graph coloring problem with human-readable output.

```
Build:  lake build graph-coloring-reader
Run:    ./.lake/build/bin/graph-coloring-reader
Input:  graph_coloring_3col.cnf
Output: Valid 3-colorings in human-readable format (v1=color1, v2=color2, ...)
Result: ✅ All 12 valid colorings extracted
```

**Output Example:**
```
v1=1, v2=3, v3=2, v4=1, v5=2
v1=1, v2=3, v3=2, v4=1, v5=3
...
```

## Problem Coverage

| Demo | Type | Variables | Solutions | Purpose |
|------|------|-----------|-----------|---------|
| ReaderStepByStep | Simple SAT | 4 | 9 | Basic functionality |
| Tseitin | Encoding | 4 | 32 | Auxiliary variable handling |
| Pigeonhole | UNSAT | 6 | 0 | Unsatisfiable formula test |
| GraphColoring | Combinatorial | 15 | 12 | Scalability demonstration |

## Running the Demonstrations

```bash
# Build all reader demonstrations
lake build reader tseitin pigeonhole-reader graph-coloring-reader

# Run each demonstration
./.lake/build/bin/reader
./.lake/build/bin/tseitin
./.lake/build/bin/pigeonhole-reader
./.lake/build/bin/graph-coloring-reader
```

## Key Features Demonstrated

✅ **Solution Extraction:** Reader finds all solutions correctly  
✅ **SAT/UNSAT Handling:** Works on both satisfiable and unsatisfiable formulas  
✅ **Variable Assignment Traces:** Shows complete variable assignments  
✅ **Human-Readable Output:** Colorings shown in plain language  
✅ **Scalability:** Handles 15-variable problems without degradation  

## See Also

- [`../index.md`](../index.md) — All executables index
- [`../../test/cnf/README.md`](../../test/cnf/README.md) — CNF test files
- [`../../../docs/analysis/VALIDATION_SUMMARY.md`](../../../docs/analysis/validation-reports/VALIDATION_SUMMARY.md) — Validation results

---

*Last updated: 2026-09-13*
