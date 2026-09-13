# Theorem 03: completeness_pure

**A satisfiable well-formed formula is reported SAT. No open hypothesis.**

## Formal statement (proven)

```lean
theorem completeness_pure (cnf : Cnf) (hwf : WF cnf) (h : Satisfiable cnf) :
    is_satisfiable (run_pure cnf) = true
```

Location: `lean_project/AbsSat/SatMachine/PureProofs.lean`. Axioms: `propext`, `Quot.sound`.

## Hypotheses

- **`WF cnf`** (`AbsSat/Cnf/Formula.lean`): every literal's variable is below `nVars`,
  and the three literals of a clause sit at distinct map steps. The earlier statement
  (`Sat a cnf → …`) omitted it, but the driver theorems it rests on require it.
- `Satisfiable cnf` is `∃ a : Assign, Sat a cnf`.

## Proof

1. `stepCount_pos`: `stepCount cnf = 2·nVars + #clauses + 2 > 0`.
2. `pureRun_ne_nil` (`GraphPath/Model/PureDriver.lean`): for a `WF`, satisfiable formula
   the last line of `pureRun` is non-empty. It rests on `pureRun_carries`: the satisfying
   assignment names a branch of the map, and every driver step either leaves that
   branch's state alone or merges another branch into it — neither destroys it.
3. `is_satisfiable_run_pure_iff` (built on Theorem 01) transfers this to the machine.

## Correction to the earlier plan

This file previously cited `completeness_theorem` from
`SatMachine/Model/Completeness.lean`. That theorem is about a different machine
(`PureGMap`, `Model.run_pure`) that only shares the name `run_pure`. The result that
actually applies is `pureRun_ne_nil`.

## Stronger form already available

`pureRun_full_state` (`PureDriver.lean`) says more than non-emptiness: for a satisfying
assignment `a`, the last line has an entry at `a`'s final map node whose state spans the
whole map, is valid, and is inhabited.
