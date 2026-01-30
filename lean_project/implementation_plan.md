# Algorithm Migration Plan

## Goal Description
Migrate the core SAT solving logic (`SatMachine`, `GraphPath` logic, `GraphPow`) from the legacy Julia codebase to Lean 4, completing Phase 2 of the project.

## User Review Required
> [!IMPORTANT]
> The original `GraphPath.lean` contained placeholder structures. These will be replaced by the actual DB components (`AbsSat.Db.Path.Cols`).

## Proposed Changes

### AbsSat/GraphPath
#### [MODIFY] [GraphPath.lean](file:///home/ricardo/Documentos/workspace/research/jules_lean4_research/lean_project/AbsSat/GraphPath/GraphPath.lean)
- Replace placeholder structs with imports from `AbsSat.Db`.
- Implement `do_up!` and filtering logic.

### AbsSat/SatMachine
#### [NEW] [SatMachine.lean](file:///home/ricardo/Documentos/workspace/research/jules_lean4_research/lean_project/AbsSat/SatMachine/SatMachine.lean)
- Port `SatMachine` module.
- Implement the recursive execution loop.

### AbsSat/GraphPow
#### [NEW] [GraphPow.lean](file:///home/ricardo/Documentos/workspace/research/jules_lean4_research/lean_project/AbsSat/GraphPow/GraphPow.lean)
- Port `GraphPow` module.

## Verification Plan
### Automated Tests
- Run `lake build` to ensure type safety.
- Create a test runner that solves `test.cnf` using the new `SatMachine`.
- Assert that `SatMachine` output matches `ExhaustiveSolver` output for small instances.
