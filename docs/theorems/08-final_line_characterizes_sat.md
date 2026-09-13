# Theorem 08: the final line characterizes SAT

**UNSAT is detected as an empty final line.** This splits into a structural part that
holds for every formula and a semantic part that needs `ClauseStepExact`. Both are
proven in `lean_project/AbsSat/SatMachine/PureProofs.lean` (axioms: `propext`,
`Quot.sound`).

## 1. Structural, unconditional

```lean
theorem is_satisfiable_run_pure_iff (cnf : Cnf) :
    is_satisfiable (run_pure cnf) = true ↔ pureRun cnf ≠ []
```

The machine says UNSAT exactly when `PureDriver`'s last line is empty. Proof: Theorem 01
(`run_pure_getLast?`) identifies the machine's last timeline row with `pureRun cnf`,
then unfold `is_satisfiable`.

## 2. Semantic

- **Satisfiable ⇒ final line non-empty**, for every `WF` formula:
  `completeness_pure` / `pureRun_ne_nil`.
- **Final line non-empty ⇒ satisfiable**, under `ClauseStepExact`: `soundness_pure`.
  Every entry of the last line is valid (`StateOk.valid`), and `Decision.lean` decodes a
  valid final state into a satisfying assignment once `ClauseStepExact` holds.

Together: `run_pure_decides` —
`is_satisfiable (run_pure cnf) = true ↔ Satisfiable cnf` for `WF` formulas satisfying
`ClauseStepExact`.

## Correction to the earlier plan

The earlier statement used `(run_pure cnf).timeline.last?.isSome`. The timeline always
has at least the seed row, so that expression is always `true` and characterizes
nothing. What matters is the *content* of the last row, which is `pureRun cnf`.

## What a non-empty final line holds

`pureRun_full_state` (`PureDriver.lean`): for a satisfying assignment `a`, the entry at
`a`'s final map node spans the whole map, is valid, and is inhabited; `L7.sat_of_inhabited`
reads a solution out of an inhabited state. Doing the same for an *arbitrary* final
state — rather than one known to lie on a solution branch — is precisely what
`ClauseStepExact` supplies, and is the open problem.
