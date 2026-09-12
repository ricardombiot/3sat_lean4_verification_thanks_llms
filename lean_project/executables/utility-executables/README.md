# Utility Executables

Collection of utility tools for analysis, testing, and graph manipulation.

## Quick Reference

| Executable | Purpose | Build Command |
|------------|---------|---|
| Test2LitMain | Test 2-literal clause support | `lake build test-2lit` |
| StepByStepMain | Step-by-step SAT machine execution | `lake build runTests` |
| StepByStepCNFMain | CNF step-by-step processing | `lake build stepbystep-cnf` |
| CnfMapMain | CNF to graph map conversion | `lake build cnfmap` |
| DiffMain | Difference/comparison tool | `lake build diffTest` |
| VisualizeGPathMain | Graph path visualization | `lake build visualize` |
| L6SearchMain | L6 search variant | `lake build l6search` |
| WidthMain | Width calculation | `lake build width` |
| HyperMain | Hyper-graph utilities | `lake build hyper` |
| ExtendMain | Extension utilities | `lake build extend` |
| ValidateMain | General validation tool | `lake build validate` |

## Purpose of Each Tool

### Test2LitMain
Tests support for 2-literal clauses in CNF parser.

**Used for:** Validating CNF parser fix for 2-literal clause handling  
**Input:** test_2lit.cnf (simple 2-variable formula with 2-literal clauses)

### StepByStepMain & StepByStepCNFMain
Debug tools for observing machine execution step-by-step.

**Use case:** Understanding search tree construction and variable assignment progression  
**Output:** Machine state at each step

### CnfMapMain
Converts CNF formulas to internal graph map representation.

**Use case:** Debugging CNF import and internal representation  
**Output:** Graph structure visualization/analysis

### DiffMain
Compares different CNF instances or execution traces.

**Use case:** Finding differences between two SAT instances

### VisualizeGPathMain
Generates visualization of graph path structures.

**Output:** DOT and PNG files showing graph topology  
**Note:** Requires GraphViz for PNG rendering

### Search & Graph Analysis Tools
L6SearchMain, WidthMain, HyperMain — specialized search and graph analysis variants.

**Use case:** Exploring different SAT solving strategies and graph properties

### ValidateMain
General-purpose validation framework.

**Use case:** Custom validation scenarios

## Building & Running

```bash
# Build all utility executables
lake build runTests diffTest l6search width hyper extend cnfmap \
           stepbystep stepbystep-cnf visualize validate test-2lit

# Run a specific utility
./.lake/build/bin/<executable-name>
```

## Development & Testing

These tools support development, debugging, and exploration of:
- CNF parser functionality
- Graph path construction
- Timeline and machine state
- Search strategies
- Graph visualization

## See Also

- [`../index.md`](../index.md) — All executables index
- [`../validation-tools/README.md`](../validation-tools/README.md) — Validation tools
- [`../reader-demonstrations/README.md`](../reader-demonstrations/README.md) — Reader demonstrations
- [`../../test/cnf/README.md`](../../test/cnf/README.md) — CNF test files

---

*Last updated: 2026-09-13*
