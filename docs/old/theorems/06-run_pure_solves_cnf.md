# Theorem 06: run_pure_decides

**Under `ClauseStepExact`, the pure machine decides 3SAT.**

(Formerly planned as `run_pure_solves_cnf`, with an unconditional statement that is not
proven — see below.)

## Formal statement (proven)

```lean
theorem run_pure_decides (cnf : Cnf) (hwf : WF cnf) (hexact : ClauseStepExact cnf) :
    is_satisfiable (run_pure cnf) = true ↔ Satisfiable cnf
```

Location: `lean_project/AbsSat/SatMachine/PureProofs.lean`. Axioms: `propext`, `Quot.sound`.

Proof: `⟨soundness_pure cnf hwf hexact, completeness_pure cnf hwf⟩`.

## What each direction needs

| Direction | Theorem | Hypotheses |
|-----------|---------|------------|
| SAT verdict → satisfiable | [02 `soundness_pure`](02-soundness_pure.md) | `WF`, **`ClauseStepExact` (open)** |
| satisfiable → SAT verdict | [03 `completeness_pure`](03-completeness_pure.md) | `WF` only |

## Why the earlier statement was wrong

The plan stated `is_satisfiable (run_pure cnf) = true ↔ ∃ a, Sat a cnf` with no
hypotheses, as a combination of two "already proven" theorems. Both of those citations
pointed at a different machine (`SatMachine/Model`). For `SatMachinePure`:

- the `←` direction needs `WF` (and is proven);
- the `→` direction is exactly the open problem `ClauseStepExact`. Proving the
  unconditional statement for every formula would, per `Decision.lean`, put 3SAT in P.

## Open work

Discharge `ClauseStepExact` — globally or for a class of formulas. The UNSAT form
(`is_satisfiable (run_pure cnf) = false ↔ ¬ Satisfiable cnf`) follows from
`run_pure_decides` by a Bool case split; it is not yet stated in Lean.
