# 3sat_lean4_verification_thanks_llms

This repository contains one attempt at the formal verification of the **AbsSat** algorithm, a 3-SAT solver based on "Exponential Abstractions" and structural graph compression. The core logic has been migrated from Julia to **Lean 4** to provide mathematical guarantees of correctness.

## Project Vision

AbsSat does not search for one satisfying assignment. It **builds, step by step, a compressed graph that contains every satisfying assignment of a 3-SAT formula at once**, one clique per solution, and then reads a solution out of it. The algorithm abstracts the search space into a layered directed acyclic graph whose width is bounded by the static structure of the formula: each step of the map has at most 7 nodes (classic map) or 2 nodes (binary map), and a state never stores paths, only compatibilities between nodes. The Lean 4 work proves what this graph represents and isolates what is still needed for the reading to be cheap.

### 1. The map: paths are assignments

The formula φ is compiled into a **map**, a graph with one layer per step: a step per variable value (`v = 0`, `v = 1`), a step for its negation, and steps for the clauses. In the classic map a clause is one step whose 7 nodes are the 7 rows that satisfy it; in the binary map a clause is three steps of two nodes, each copying one literal, and the disjunction is a **forbidden window** `(0,0,0)` that the construction never creates. Every node may *require* nodes of earlier steps (a negation requires the opposite value, a clause row requires its literals).

A path through the map that respects the requirements is exactly the branch of an assignment that satisfies the clauses it has crossed ([`ids_of_reqSat`](./lean_project/AbsSat/GraphPath/Model/ConservationPrefix.lean#L479)), and every such path decodes to a model of φ ([`path_is_solution`](./lean_project/AbsSat/GraphPath/Model/LiveSolution.lean#L51), [`sat_of_carried`](./lean/improves_bingo/AbsSatBingo/Model/Decode.lean#L169)).

### 2. The machine: one graph, all the solutions

The machine walks the map step by step. A **state** holds the live path nodes of one step of the map (its *key*), where each path node remembers a window of its history (`(node, parent, grandparent)`), and a relation of **compatibility** between them: the *owner tables* of [`lean_project`](./lean_project) and [`lean/improves_bin`](./lean/improves_bin), or the *owner graph* of [`lean/improves_bingo`](./lean/improves_bingo), plus, in its latest version, a list of **forbidden triples**. Four operations build it:

* **filter**: when the state is sent to a child of the map, the nodes that contradict the child's requirements are removed;
* **review**: a pruning to a fixed point that deletes every node and every compatibility that cannot be on a solution as far as the local rules can see (cleaning, coherence with parents and children, the pair rule, and the triple rule);
* **UP**: the child is added as a new layer, and each new node inherits the compatibilities of its parents ([`upOn`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOn.lean#L256));
* **join**: all the states that reach the same node of the map are merged into one ([`joinOn`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOn.lean#L182)). This is where the compression happens: histories with different pasts, and different futures, share the same nodes.

A **clique** of a state (one node per step, pairwise compatible, consecutive nodes linked) is the branch of one assignment. What is proved:

* **No solution is ever lost.** For every satisfying assignment, the final line of the machine carries its clique, through every filter, review, UP and join ([`pureRunW_ne_nil`](./lean_project/AbsSat/GraphPath/Model/ConservationImproves.lean#L207), [`run_carries`](./lean/improves_bingo/AbsSatBingo/Model/Machine.lean#L485), [`run_carriesOn`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnMachine.lean#L512); no rule of the review can delete a carried clique, [`carried_review`](./lean/improves_bingo/AbsSatBingo/Model/Keeps.lean#L363)). The same holds for partial solutions at every step ([`pureStepsW_chain_below`](./lean_project/AbsSat/GraphPath/Model/ConservationPrefix.lean#L400)).
* **No false solution is ever created.** Every clique of a state is a genuine branch ([`genuine_of_chain`](./lean_project/AbsSat/GraphPath/Model/RunNoBorrow.lean#L347), [`validSel_of_carried`](./lean/improves_bingo/AbsSatBingo/Model/CliqueSplit.lean#L326)); a clique in the final line is a model of φ ([`sat_of_carried`](./lean/improves_bingo/AbsSatBingo/Model/Decode.lean#L169)). Joins never mix branches: a clique of the union of two arrivals is a clique of one of them ([`noBorrow_at_insert`](./lean_project/AbsSat/GraphPath/Model/RunNoBorrow.lean#L531), [`cliqueSplit`](./lean/improves_bingo/AbsSatBingo/Model/CliqueSplit.lean#L372)).
* Together: **the set of paths represented by the final states is exactly the set of certificates of φ**, and it is non-empty iff φ is satisfiable ([`machineSet_complete`](./lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L74), [`machineSet_sound`](./lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L112), [`machineSet_nonempty_iff`](./lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L124)). The machine is the brute-force oracle — which would list every satisfying assignment — stored in compressed form: compatibilities between pairs (and forbidden triples) instead of a list of paths. Measured, each state equals, table by table, the union of the oracle's paths that reach its key (v139).

### 3. What the compression keeps, and what it may not

The tables never forget: every compatibility realised by a solution is in them ([`tablesComplete`](./lean_project/AbsSat/GraphPath/Model/Exactness.lean#L67)). The hard question is the converse, whether every compatibility the machine keeps belongs to *some* solution, and whether the pieces that remain always fit together into a whole clique. Pairwise information is not enough in general: there are states closed under all pairwise rules with no clique at all ([`closed_not_chainInv`](./lean/improves_bingo/AbsSatBingo/Model/ClosedLimit.lean#L201)), and a formula can produce a "dead triangle" of three compatible pairs that no single solution contains (v191).

The latest machine settles exactly where this can happen. **The machine with forbidden triples is exact in all its states if and only if the formula has no *phantom families*** ([`machineExact_iff`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnTight.lean#L509), weak form [`machineExactW_iff`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L158)), a closure property of sets of assignments that does not mention the machine. When it holds, every node and every compatibility left in a state lies on a solution.

### 4. Reading a solution

The **reader** fixes one choice at a time (a node of a step with several options) and re-runs the review, which deletes everything incompatible with that choice; the solution is the single clique left at the end.

* With backtracking, the reader decides 3-SAT with no hypothesis ([`readerVerdictBT_iff`](./lean_project/AbsSat/GraphPath/Model/ReaderBT.lean#L267)); the answers are always correct and come with a certificate checked against φ ([`answer_unsat_sound`](./lean_project/AbsSat/GraphPath/Model/Answer.lean#L93), [`answer_sat_sound`](./lean_project/AbsSat/GraphPath/Model/Answer.lean#L101), [`verdictOn_certified`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnTop.lean#L336)).
* Without backtracking, whatever it returns is a model ([`readerVerdictW_sound`](./lean_project/AbsSat/GraphPath/Model/ReaderExec.lean#L149)). That it **never gets stuck** is proved for whole classes of formulas — 2-CNF shape, blocks, chains of up to five blocks, and chains of up to six blocks given the lines — ([`reader_on_twoLike`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L181), [`reader_chain4Cross_any`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L293), [`reader_sep_chain5Cross_full`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L404), [`reader_bisect`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L489)), follows in general from the absence of phantom families ([`reader_on`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L155)), and has never failed in any measurement (backtracking was never needed).

The cost of the machine is a separate matter: the correctness theorems above say nothing about time or space, and the design goal of keeping each state small is pursued by the compression in the join and is measured, not proved, here.

## What's Inside?

### Three Lean 4 projects, one per version of the machine

| project | folder | namespace | machine it models | size |
|---|---|---|---|---|
| **AbsSat** | [`lean_project/`](./lean_project) | `AbsSat` | the pure machine and the *Improves* machine on the **classic map** (one step per clause, with its 7 satisfying rows); owners stored as a **table per node** | 277 files, ~103k lines |
| **AbsSatBin** | [`lean/improves_bin/`](./lean/improves_bin) | `AbsSatBin` | the same machine on the **binary map** (each clause is 3 steps of 2 nodes plus a forbidden window `(0,0,0)` that encodes the disjunction) | 124 files, ~43k lines |
| **AbsSatBingo** | [`lean/improves_bingo/`](./lean/improves_bingo) | `AbsSatBingo` | the bin machine with owners stored as a **graph of edges** per state; since v217 also with **forbidden triples** (`FORBID = :on`), parametrised by mode (`runM .off` is the old machine by `rfl`) | 156 files, ~52k lines |

`AbsSatBingo` imports its base layer (CNF, binary map, node identifiers) from `AbsSatBin` as a Lake dependency. None of the three projects contains `sorry`; every project builds with `warningAsError`, and the theorems depend only on the standard axioms (`propext`, `Quot.sound`, and in parts of `AbsSatBingo` `Classical.choice`).

### The Julia ⇄ Lean 4 mirror

Each Lean project is the mirror of a Julia implementation, and the two are kept in lock-step:

| Julia (executable machine) | Lean 4 (model + proofs) | how they are compared |
|---|---|---|
| [`julia/improves`](./julia/improves) | `lean_project` | `Probes/ExecDiff.lean` (`exec-diff`, 500/500 against the exhaustive oracle), `diffTest` |
| [`julia/improves_bin`](./julia/improves_bin) | `lean/improves_bin` | `lean/improves_bin/scripts/diff_map_bin.sh` (the map, 74/74), `driverbin-check` (machine and reader against brute force) |
| [`julia/improves_bingo`](./julia/improves_bingo) | `lean/improves_bingo` | `bingo-dump` vs `test_3sat/dump_final.jl` / `dump_forbid.jl`, compared by `test_3sat/compare_bingo.jl` (final states, triples included); `bingo-check`, `tagged-check` |

The methodology, as it emerged in the bitácora:

1. **Change the machine in Julia first**, behind a switch (`CLEAN_MODE`, `SYM_MODE`, `PAIR_MODE`, `FINAL_CHECK`, `FORBID`, `ROW_TAGS` …), and run a **differential** against the previous machine and the exhaustive solver (same verdicts, same solutions, same final states, same review rounds).
2. **Mirror the change in Lean** as a *specification* (flat lists, derived validity), with the old behaviour kept definitionally equal, and compare dumps Lean ⇄ Julia on small instances before proving anything on top.
3. **Measure every hypothesis with a probe before trying to prove it**, in the **same mode** as the Lean statement it backs (v216), on small instances without sampling and on larger ones (`v7`) before building a chain on it. Probes live in [`julia/improves_bingo/test_3sat/`](./julia/improves_bingo/test_3sat) and [`lean_project/Probes/`](./lean_project/Probes), always under a memory cap (`test_3sat/run_capped.sh`).
4. **Keep a sync table** with one row per piece, name and mode: [`docs/plans/lean_bingo.md`](./docs/plans/lean_bingo.md) (and [`docs/plans/lean_forbid_on.md`](./docs/plans/lean_forbid_on.md) for the forbidden-triples mirror).
5. **Adopt a machine change only if it does not change what the machine decides** and it makes something provable (two-phase cleaning, symmetric review, pair rule, final check); otherwise retire it and keep it recoverable in git (the key-row tags of v196–v198).

### Documentation

*   **Summary of the proofs**: [`docs/resumen_demostraciones.md`](./docs/resumen_demostraciones.md) (Spanish) consolidates reports v126–v225 project by project, with every theorem linked to file and line, the abandoned routes and the open hypotheses.
*   **The bitácora**: [`docs/bitacora/`](./docs/bitacora), 225 first-person reports (`verificacion_inseguridad_autor_vNNN.md`) written by the LLM that did each round of work, addressed to the author: what was proved, measured, refuted and proposed.
*   **Technical context and plans**: [`docs/context/escalera_reader.md`](./docs/context/escalera_reader.md) (the reader's ladder in detail), [`docs/plans/`](./docs/plans) (binary map, graph owners, pair mode, symmetric review, row tags, forbidden triples).
*   **Complexity Analysis**: Detailed proofs of the $O(S^4)$ time complexity and structural boundedness.
*   **Human-AI Documentation**: A series of documents detailing the collaborative process between the author and various LLMs (Gemini, Deepseek, Claude).

## What Is Proved

Every entry below is a Lean 4 theorem without `sorry` and **without open hypotheses**, unless the hypothesis is named.

### Soundness of the answers and completeness of the machines

| statement | theorem |
|---|---|
| If *Improves* ends with no state, φ is unsatisfiable (the machine never loses a solution) | [`pureRunW_ne_nil`](./lean_project/AbsSat/GraphPath/Model/ConservationImproves.lean#L207) |
| Every UNSAT answer is correct; every SAT answer carries a checked model | [`answer_unsat_sound`](./lean_project/AbsSat/GraphPath/Model/Answer.lean#L93), [`answer_sat_sound`](./lean_project/AbsSat/GraphPath/Model/Answer.lean#L101) |
| The set of paths the machine stores is **exactly** the set of certificates of φ | [`machineSet_complete`](./lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L74), [`machineSet_sound`](./lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L112), [`machineSet_nonempty_iff`](./lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L124) |
| The machine loses no partial solution; joins never borrow paths between branches | [`pureStepsW_chain_below`](./lean_project/AbsSat/GraphPath/Model/ConservationPrefix.lean#L400), [`noBorrow_at_insert`](./lean_project/AbsSat/GraphPath/Model/RunNoBorrow.lean#L531) |
| **The machine decides 3-SAT with a backtracking reader** | [`readerVerdictBT_iff`](./lean_project/AbsSat/GraphPath/Model/ReaderBT.lean#L267) |
| The non-backtracking reader, when it finishes, returns a model | [`readerVerdictW_sound`](./lean_project/AbsSat/GraphPath/Model/ReaderExec.lean#L149), [`readerVerdictW_sound`](./lean/improves_bin/AbsSatBin/GraphPath/Model/ReaderExec.lean#L152) |
| Completeness of the binary-map machine; of the graph-owners machine; of the machine with forbidden triples | [`completeness_pure`](./lean/improves_bin/AbsSatBin/SatMachine/PureProofs.lean#L126), [`machineVerdict_of_sat`](./lean/improves_bingo/AbsSatBingo/Model/Machine.lean#L502), [`machineVerdictOn_of_sat`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnMachine.lean#L529) |
| Both defined answers of the machine with triples are certified | [`verdictOn_certified`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnTop.lean#L336) |

### Structural invariants of the machine

| statement | theorem |
|---|---|
| All tables of the bin machine are symmetric; the aggressive review equals the normal one along the reader | [`symInv_reachable`](./lean/improves_bin/AbsSatBin/GraphPath/Model/SymMachine.lean#L214), [`reviewAgg_eq_review`](./lean/improves_bin/AbsSatBin/GraphPath/Model/PairInactive.lean#L742) |
| Every state of the bin machine is a *kernel*; the review never goes below a kernel | [`kernel_reachable`](./lean/improves_bin/AbsSatBin/GraphPath/Model/KernelUp.lean#L636), [`below_review`](./lean/improves_bin/AbsSatBin/GraphPath/Model/Kernel.lean#L579) |
| Two-phase cleaning leaves no dead ids and only valid nodes, and loses no solution | [`owners_live_cleanInvalid₂`](./lean_project/AbsSat/GraphPath/Model/CleanTwoPhase.lean#L118), [`isValidNode_cleanInvalid₂`](./lean_project/AbsSat/GraphPath/Model/CleanTwoPhase.lean#L256), [`ChainSound_cleanInvalid₂`](./lean_project/AbsSat/GraphPath/Model/CleanInvalid.lean#L627) |
| With the pair rule, the aggressive sweep is the identity at the fixpoint | [`aggInactive_of_revOk`](./lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L205), [`aggSweep_eq_self`](./lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L195) |
| With the final check, every state left by the review is closed | [`closedState_review`](./lean/improves_bingo/AbsSatBingo/Model/ClosedReview.lean#L403) |
| A clique of the union of two arrivals is a clique of one side | [`cliqueSplit`](./lean/improves_bingo/AbsSatBingo/Model/CliqueSplit.lean#L372) |
| In every join of the machine with triples, every live top of the reviewed union is live in one side | [`topSideAt_nil_line`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnNoPin.lean#L290) |

### The verdict reduced to a statement about the formula

| statement | theorem |
|---|---|
| **The machine with triples is exact in all its states iff φ has no *phantom families*** (a closure property of sets of assignments that does not mention the machine) | [`machineExact_iff`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnTight.lean#L509); weak form [`machineExactW_iff`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L158) |
| Without phantom families the machine decides and the reader never backtracks | [`spineVerdictOn_iff_of_phantomFree`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnHelly.lean#L762), [`reader_on`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L155) |
| The reader is exact iff the reading has no phantom families | [`readerExact_iff`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnReadIff.lean#L129), [`readerExactW_iff`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L295) |

### Classes of formulas decided with no hypothesis

| class | machine exact / verdict | reader without backtracking |
|---|---|---|
| formulas with 2-CNF shape | [`spineVerdictOn_iff_of_twoLike`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnMaj.lean#L1016) | [`reader_on_twoLike`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L181) |
| clauses in disjoint blocks of ≤ 3 variables | [`machineExact_of_blocks`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnBlock.lean#L285) | — |
| two blocks sharing one variable | [`machineExact_of_sep2`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnSep.lean#L671) | — |
| chains of three blocks | [`machineExact_threeChain`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain.lean#L959) | — |
| `chain4_cross` (four blocks, crossed numbering) | [`machineExact_chain4Cross`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L289) | [`reader_chain4Cross_any`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L293) |
| `chain5_cross` | [`machineExact_chain5Cross`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L395), [`spineVerdictOn_iff_chain5Cross`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L399) | [`reader_sep_chain5Cross_full`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L404) |
| the five-block class `Chain5C`, any numbering | [`machineExact_of_chain5C`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5C.lean#L655) | — |
| `ChainN` up to six blocks, **given the lines** | — | [`reader_bisect`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L489) |

The reader that closes the chains is the **separators-first reader** (fix the variables shared by several clauses first; [`reader_sep_on`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnSepRead.lean#L217)), which changes only the reading order, not what the machine computes.

## What Is Open

| question | where | status |
|---|---|---|
| Does every 3-CNF satisfy `PhantomAtW` (no phantom families, weak form)? | [`PhantomAtW`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L57) | **open**; equivalent to the exactness of the machine with triples. The strong form `PhantomAt` is **false** in general (`chain6_cross`, v223) |
| The lines of `ChainN` for longer chains; `PinPairs` for a reader in any order | [`PinPairs`](./lean/improves_bingo/AbsSatBingo/Model/ForbidOnPinPairs.lean#L39) | open; proved in the classes above. The reader in any order is **not** exact on `chain5_cross` (36 phantom triangles), yet it never gets stuck |
| `M1aAll` and `KFix` in every join of the bin machine | [`M1aAll`](./lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean#L43), [`KFix`](./lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean#L66) | open, measured without failure |
| `PinnedUnionInhabited` for `ImprovesCima` | [`sat_of_pinnedUnionInhabited`](./lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L2451) | open; equivalent to the verdict |
| The cost of the non-backtracking reader | — | the backtracking reader decides without hypotheses; measured, backtracking is never needed |

Many intermediate hypotheses were refuted on the way (`CommonOwner`-style local rules, `SegGood` on seed 11, `MapCert`, `PrevCut`, `Star4At`, …); the full list, with the measurement that refuted each one, is in [`docs/resumen_demostraciones.md`](./docs/resumen_demostraciones.md) §5.

## The Book
The original theory behind `AbsSat` — "P vs. NP - En busca del algoritmo 'imposible' para 3SAT" — is written up in full (Spanish) in [book/book_3sat_es.pdf](./book/book_3sat_es.pdf). Start there for the conceptual background before diving into the Lean 4 formalization.

## Getting Started
Please refer to [README_VERIFICATION.md](./lean_project/README_VERIFICATION.md) for a detailed index of the earlier verification and analysis documents, and to [`docs/resumen_demostraciones.md`](./docs/resumen_demostraciones.md) for the current state.

To build the projects:
```bash
(cd lean_project && lake build AbsSat)
(cd lean/improves_bin && lake build)
(cd lean/improves_bingo && lake build)
```

## Collaboration Credits
This project is a testament to modern human-AI collaboration:
- **Author**: Original theory, Julia implementation, and conceptual design.
- **Deepseek**: Technical planning and structural design of the Lean 4 migration.
- **Gemini (Jules/Antigravity)**: Implementation of Lean 4 code, formal verification, and complexity analysis.
- **Claude (Sonnet 5 & Fable 5)**: Review and propose important improves.
- **Fable 5 & DeepSeek Pro V4**: Formal Verification of the GPathM Owners Invariant in Lean 4
- **Claude (Opus 5 & Opus 5.5)**: The bitácora reports v126–v225, the Julia ⇄ Lean mirrors of the binary map, the graph owners and the forbidden triples, and the proofs summarized above.
