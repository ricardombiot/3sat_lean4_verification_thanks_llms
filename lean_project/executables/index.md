# Lean 4 Executable Entry Points

This directory contains all executable Lean 4 programs organized by function. Each subdirectory groups related executables with their documentation.

## Directory Structure

### [validation-tools/](validation-tools/)
Brute-force validators that enumerate all possible assignments and verify Reader correctness.

**Executables:**
- `ValidateTseitin.lean` — Validates Reader on Tseitin encoding (32 solutions)
- `ValidatePigeonhole.lean` — Validates Reader on Pigeonhole formula (UNSAT)
- `ValidateGraphColoring.lean` — Validates Reader on graph coloring (12 solutions)

**Build:** `lake build tseitin-validate`, `lake build pigeonhole-validate`, `lake build graph-coloring-validate`

### [reader-demonstrations/](reader-demonstrations/)
Step-by-step execution examples showing how the Reader extracts solutions from various formulas.

**Executables:**
- `ReaderStepByStepMain.lean` — Reader on test_sat_medium.cnf (9 solutions)
- `TseitinReaderMain.lean` — Reader on Tseitin formula
- `PigeonholeReaderMain.lean` — Reader on Pigeonhole formula (UNSAT demo)
- `GraphColoringReaderMain.lean` — Reader extracting valid colorings

**Build:** `lake build reader`, `lake build tseitin`, `lake build pigeonhole-reader`, `lake build graph-coloring-reader`

### [utility-executables/](utility-executables/)
Various utility programs for analysis, testing, and graph manipulation.

**Executables:**
- `Test2LitMain.lean` — Tests 2-literal clause support
- `StepByStepMain.lean` — Step-by-step SAT machine execution
- `StepByStepCNFMain.lean` — CNF step-by-step processing
- `CnfMapMain.lean` — CNF to graph map conversion
- `DiffMain.lean` — Difference/comparison tool
- `VisualizeGPathMain.lean` — Graph path visualization
- `L6SearchMain.lean` — L6 search variant
- `WidthMain.lean` — Width calculation
- `HyperMain.lean` — Hyper-graph utilities
- `ExtendMain.lean` — Extension utilities
- `ValidateMain.lean` — General validation tool

**Build:** See lakefile.toml for individual build commands

## Building Executables

All executables can be built with:
```bash
cd lean_project
lake build <executable-name>
```

For validation executables:
```bash
lake build tseitin-validate    # Tseitin validator
lake build pigeonhole-validate # Pigeonhole validator
lake build graph-coloring-validate # Graph coloring validator
```

## See Also

- [`lakefile-config.md`](lakefile-config.md) — Guide to lakefile.toml configuration
- [`validation-tools/README.md`](validation-tools/README.md) — Validator documentation
- [`reader-demonstrations/README.md`](reader-demonstrations/README.md) — Reader demo documentation
- [`utility-executables/README.md`](utility-executables/README.md) — Utility tools documentation

---

*Last updated: 2026-09-13*
