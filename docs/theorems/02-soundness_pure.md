# Theorem 02: soundness_pure

**A SAT verdict is backed by a satisfying assignment — assuming `ClauseStepExact`.**

## Formal statement (proven)

```lean
theorem soundness_pure (cnf : Cnf) (hwf : WF cnf) (hexact : ClauseStepExact cnf)
    (h : is_satisfiable (run_pure cnf) = true) : Satisfiable cnf
```

Location: `lean_project/AbsSat/SatMachine/PureProofs.lean`. Axioms: `propext`, `Quot.sound`.

## Hypotheses

- **`WF cnf`** (`AbsSat/Cnf/Formula.lean`): every literal's variable is below `nVars`,
  and the three literals of a clause sit at distinct map steps.
- **`ClauseStepExact cnf`** (`AbsSat/GraphPath/Model/NodeInvariant.lean`) — **open**.
  At every clause step (strictly between the literal block and the fusion steps),
  filtering a reachable, valid, supported state by that step's requirements keeps it
  supported whenever it stays valid. `Decision.lean` notes that, since the run is
  polynomial, holding for every formula this would put 3SAT in P.

`ClauseStepExact` is a theorem parameter, never an `axiom`: every result that depends
on it says so in its signature, and `#print axioms` stays clean.

## Proof

1. `is_satisfiable_run_pure_iff` (built on Theorem 01): the verdict is SAT exactly when
   `pureRun cnf ≠ []`.
2. Take an entry `kv` of that last line. `stateOk_pureRun` (`Decision.lean`) gives
   `StateOk`, whose `valid` field is `isValid kv.2 = true`.
3. `decides_of_ClauseStepExact` (`Decision.lean`) turns a valid final state into
   `Satisfiable cnf`.

## Correction to the earlier plan

This file previously proposed reusing `soundness_theorem` from
`SatMachine/Model/Soundness.lean`, with no extra hypothesis. That theorem is about a
different machine (`PureGMap`, `Model.run_pure`) that only shares the name `run_pure`;
it says nothing about `SatMachinePure`. Soundness of this machine is exactly where the
open problem lives.

## Open work

Prove `ClauseStepExact` — for every well-formed formula, or for a class of formulas —
and pass it as the argument. Nothing in this proof has to change.
