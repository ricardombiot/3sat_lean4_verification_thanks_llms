# Lakefile Configuration Guide

Guide to updating `lakefile.toml` to reference executables in the new `executables/` directory structure.

## Current Structure (After Reorganization)

All `.lean` executable entry points are now organized under `executables/`:

```
executables/
├── validation-tools/
│   ├── ValidateTseitin.lean
│   ├── ValidatePigeonhole.lean
│   └── ValidateGraphColoring.lean
├── reader-demonstrations/
│   ├── ReaderStepByStepMain.lean
│   ├── TseitinReaderMain.lean
│   ├── PigeonholeReaderMain.lean
│   └── GraphColoringReaderMain.lean
└── utility-executables/
    ├── Test2LitMain.lean
    ├── StepByStepMain.lean
    ├── StepByStepCNFMain.lean
    ├── CnfMapMain.lean
    ├── DiffMain.lean
    ├── VisualizeGPathMain.lean
    ├── L6SearchMain.lean
    ├── WidthMain.lean
    ├── HyperMain.lean
    ├── ExtendMain.lean
    └── ValidateMain.lean
```

## Updating lakefile.toml

### Before Reorganization
```toml
[[lean_exe]]
name = "ValidateTseitin"
root = "ValidateTseitin"

[[lean_exe]]
name = "pigeonhole-validate"
root = "ValidatePigeonhole"
```

### After Reorganization
```toml
[[lean_exe]]
name = "tseitin-validate"
root = "executables/validation-tools/ValidateTseitin"

[[lean_exe]]
name = "pigeonhole-validate"
root = "executables/validation-tools/ValidatePigeonhole"

[[lean_exe]]
name = "graph-coloring-validate"
root = "executables/validation-tools/ValidateGraphColoring"

[[lean_exe]]
name = "reader"
root = "executables/reader-demonstrations/ReaderStepByStepMain"

[[lean_exe]]
name = "tseitin"
root = "executables/reader-demonstrations/TseitinReaderMain"

[[lean_exe]]
name = "pigeonhole-reader"
root = "executables/reader-demonstrations/PigeonholeReaderMain"

[[lean_exe]]
name = "graph-coloring-reader"
root = "executables/reader-demonstrations/GraphColoringReaderMain"

# Utility executables (examples)
[[lean_exe]]
name = "test-2lit"
root = "executables/utility-executables/Test2LitMain"

[[lean_exe]]
name = "runTests"
root = "executables/utility-executables/StepByStepMain"

[[lean_exe]]
name = "stepbystep-cnf"
root = "executables/utility-executables/StepByStepCNFMain"

# ... etc for other utility executables
```

## Key Points

1. **Root paths** now include `executables/` subdirectory
2. **Executable names** (the `name` field) can stay the same or be updated
3. **File paths** must be relative to `lean_project/` directory
4. **The `.lean` extension** is NOT included in the root path

## Building Executables

After updating lakefile.toml, build executables normally:

```bash
cd lean_project
lake build <executable-name>
```

**Examples:**
```bash
lake build tseitin-validate           # Builds ValidateTseitin.lean
lake build pigeonhole-validate        # Builds ValidatePigeonhole.lean
lake build graph-coloring-validate    # Builds ValidateGraphColoring.lean
lake build reader                     # Builds ReaderStepByStepMain.lean
```

## Verification

After updating lakefile.toml:

1. **Check syntax:** `lake print-config` should show all executables
2. **Build test:** `lake build` should compile all executables
3. **Run test:** `./.lake/build/bin/<executable-name>` should execute

## Current lakefile.toml Status

⚠️ **NEEDS UPDATING** — The lakefile.toml still has old paths pointing to the root directory. Update it to reference the new `executables/` subdirectories.

### Utility Executables to Update

These all need root path updates:

```
ValidateMain → executables/utility-executables/ValidateMain
StepByStepMain → executables/utility-executables/StepByStepMain
StepByStepCNFMain → executables/utility-executables/StepByStepCNFMain
CnfMapMain → executables/utility-executables/CnfMapMain
DiffMain → executables/utility-executables/DiffMain
VisualizeGPathMain → executables/utility-executables/VisualizeGPathMain
L6SearchMain → executables/utility-executables/L6SearchMain
WidthMain → executables/utility-executables/WidthMain
HyperMain → executables/utility-executables/HyperMain
ExtendMain → executables/utility-executables/ExtendMain
Test2LitMain → executables/utility-executables/Test2LitMain
```

## Example Complete Entry

```toml
[[lean_exe]]
name = "pigeonhole-validate"
root = "executables/validation-tools/ValidatePigeonhole"
```

This tells Lake to:
- Find the main entry point in `ValidatePigeonhole.lean`
- Located at `lean_project/executables/validation-tools/ValidatePigeonhole.lean`
- Build it as executable named `pigeonhole-validate`
- Output to `.lake/build/bin/pigeonhole-validate`

---

*Last updated: 2026-09-13*
