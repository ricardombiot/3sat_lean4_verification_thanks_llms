# Formal Verification of the GPathM Owners Invariant in Lean 4

**Project**: 3-SAT verification via Lean 4 — Phase F5
**Authors**: DeepSeek Pro V4 + Claude, supervised by Ricardo M. Biot
**Date**: July 2026 (audited and corrected 2026-07-04, see §4.0)
**Lean version**: `leanprover/lean4:stable` (v4.31.0)
**Dependencies**: Std4

---

> ⚠️ **Audit status (2026-07-04): the axiomatized version of this phase is
> logically unsound.** Axiom A8 (`chain_step_eq`) is *false* for the current
> definition of `IsChain`, and `False` has been derived from it inside Lean
> (see §4.0). Axiom A9 (`addNode_preserves_ReqFiltered`) is also false as
> stated. Until both are repaired and the remaining axioms are replaced by
> proofs, **no theorem in this phase that depends on them carries evidential
> weight** — `#print axioms` shows `L1` depends on A1/A6/A7/A9 and `L1_cor`
> additionally on A2/A3/A8. The proof *architecture* (§3) is sound and two of
> the four L1 cases are genuinely proved; the repair route is concrete (§6.1).

---

## 1. Overview

This document describes the Lean 4 formalization of `ReqFiltered`, the central invariant of `GPathM` — a purely functional mirror of the executable 3-SAT Owners graph (`GPath`). The invariant states that in any well-constructed graph, whenever a requirement `req` of a node `d` shares a step with an owner `q` of `d`, the owner must be exactly that requirement:

```lean
def ReqFiltered (g : GPathM) : Prop :=
  ∀ d ∈ g.nodes, ∀ req ∈ reqOf d.id.id, ∀ q ∈ d.owners,
    q.id.step = req.step → q.id = req
```

The target result is **Lemma L1**: every graph reachable via `initSeed`, `upFiltering`, and `join` satisfies this invariant:

```lean
theorem L1 (h : Reachable reqOf g) : ReqFiltered reqOf g
```

A corollary, `L1_cor`, connects the invariant to the denotation of the graph — in any valid chain, the pairwise-ownership relation forces the identity of the selected node at each requirement step.

### Status

| Metric | Value |
|--------|-------|
| Modules | 6, plus 1 test |
| Theorems stated and type-checked | 11 (T1–T9, L1, L1_cor) |
| Proved without any axiom | 7 (T1, T2, T3, T4, T6, T9\*, and the F2 lemmas) |
| Axioms | 9 — **2 of them false as stated (A8, A9)**, 7 true and provable |
| `sorry` | 0 (but see §4.0: a false axiom is strictly worse than a `sorry`) |
| Logical consistency | **Broken while A8 is in scope** (`False` derivable) |
| Build | Library + harnesses green; 3-band differential harness passing |

\* T9 (`join_preserves_ReqFiltered`) uses only A6/A7, which are true and
provable one-liners; its own case analysis is genuine.

### Context within the larger project

This work implements Phase F5 of the [plan document](./plans/espejo_gpathm_lema_L1.md), which decomposes the bridge between the executable `GPath` and its pure mirror into six phases (F1–F6). Prior phases established the mirror data structures (F1), termination lemmas for the review loop (F2.a/F2.b), the `Reachable` inductive predicate (F3), and the chain denotation (F4). The current phase (F5) builds the invariant and the L1 induction skeleton. Phase F6 provides the differential harness validating the mirror against the executable and the brute-force oracle.

Note that the plan's definition of done for F5 is explicit: *"L1 y L1-cor sin `sorry` ni axiomas; `#print axioms` limpio."* This phase does **not** yet meet that bar.

---

## 2. Architecture

### 2.1 Module dependency graph

```
AbsSat/Utils/Alias.lean    ─── type aliases (PathNodeId, NodeId), DecidableEq
         │
         ▼
AbsSat/GraphPath/Model/GPathM.lean    ─── structures + core operations
         │                        │
         ▼                        ▼
AbsSat/GraphPath/Model/          AbsSat/GraphPath/Model/
  Reachable.lean                    Fuel.lean
  (inductive predicate)          (measure + fuel lemmas, axiom-free)
         │
         ▼
AbsSat/GraphPath/Model/Denot.lean    ─── chains, pairwise ownership
         │
         ▼
AbsSat/GraphPath/Model/OwnersInvariants.lean    ─── invariant + L1 + L1_cor
```

### 2.2 Module catalog

| Module | Role |
|--------|------|
| `Alias.lean` | Defines `NodeId` (`step : Int, index : Int`) and `PathNodeId` (`id : NodeId, parent_id : Option NodeId`). Derives `DecidableEq` for both, which also yields a **lawful** `==` via `instBEqOfDecidableEq` — enabling both `by_cases` on Prop equalities and `beq_iff_eq`. |
| `GPathM.lean` | The pure mirror: `PNodeM` (id, title, parents, sons, owners), `GPathM` (nodes, global owners, current step, map parent), and all operations: `addNode`, `review` (fuel loop), `filterRequire`, `filterAll`, `upFiltering`, `initSeed`, `mergeNode`, `join`. |
| `Reachable.lean` | Inductive predicate `Reachable reqOf : GPathM → Prop` with three constructors: `seed` (step 0, backward requirements), `up` (current step, backward/distinct requirements), `join` (with `okJoin`). |
| `Denot.lean` | Definitions: `ownersOf`, `IsChain`, `PairwiseOwned`, `pathOf`, `denot`. **Known defect:** `IsChain` does not pin the step of the selected node — this is what makes A8 false (§4.0) and must be fixed by adding `(sel k).id.step = k`, as the plan's F4 sketch specified. |
| `Fuel.lean` | Phase F2, **fully axiom-free**: `measure`, `measure_reviewPass_le` (F2.a — one pass never increases the measure) and `review_stable` (F2.b — fuel sufficiency). Its proofs unfold and reason about the same `|`-defined functions the F5 axioms claim are opaque — see §4.1. |
| `OwnersInvariants.lean` | Phase F5: `ReqFiltered` invariant, `OwnersSubset` bridge, 9 axioms (see §4.3), `pid_safe`, L1, L1_cor. |
| `MirrorTest.lean` | Phase F6: drives the **full machine loop and an exponential reader on the pure mirror**, feeding the three-band differential harness (`lake exe diffTest`): brute-force oracle vs IO executable vs pure mirror, compared on both the SAT/UNSAT verdict and the complete solution set. Acceptance run: 2,000 random instances across two seeds (261 UNSAT), zero disagreements. |

### 2.3 Why a pure mirror?

The executable `GPath` uses `IO.Ref`, `partial` functions, hash-order iteration, and mutable per-step owner tables — all of which complicate formal reasoning. `GPathM` makes three deliberate representation changes to enable proofs:

1. **Flat owners list.** `PathNodeId` carries its step in `id.step`, so owners at step `k` are a simple `List.filter` rather than a per-step table.
2. **Validity recomputed.** `isValid` checks at each call whether every step below `current_step` has a global owner, replacing the bug-prone `valid`/`emptySteps` flags.
3. **Pruning via `List.filter`.** Every narrowing operation uses `List.filter`, giving monotonicity (`pruned ⊆ previous`) from generic filter lemmas.

These changes are **specification-level**: the observable results (validity verdict, filter outcomes) match the executable, as validated by the F6 differential harness.

### 2.4 Key design decisions for provability

- **`updateAtGo` uses `List.map`.** Rewriting the recursive definition as `nodes.map (fun n => match n.id == id with | true => f n | false => n)` lets `simp`/`rw`/`List.mem_map.mp` decompose membership proofs directly. The `Fuel.lean` measure lemmas were adapted and remain axiom-free, and the three-band harness confirms the semantics did not drift.
- **`PNodeM` and `PathNodeId` derive `DecidableEq`.** This enables `by_cases h : x.id = id` (Prop equality) where convenient, and — through the lawful `==` — the `beq_iff_eq` rewrites that the axiom-elimination work needs.
- **`OwnersSubset` as a bridge.** A 4-line lemma decouples structural narrowing from the logical invariant: `OwnersSubset g g' → (ReqFiltered g → ReqFiltered g')`. It is the single-field restriction of the plan's `Pruned` relation (§7.2 of the plan), which additionally tracks `gowners ⊆` and `current_step =` — the two extra fields the axiom-elimination route needs.

---

## 3. The Invariant and the Main Theorem

### 3.1 `ReqFiltered` — owners consistency

The invariant `ReqFiltered reqOf g` asserts that for every node `d` in the graph, every requirement `req` of `d`, and every owner `q` of `d`: if `q.id.step` equals `req.step`, then `q.id` must be exactly `req`.

**Intuition.** In the 3-SAT encoding, each step of the graph corresponds to a decision point (a variable assignment or clause). Requirements are nodes from prior steps that the current node depends on. Owners are nodes that satisfy those requirements. The invariant says: at any step, there is **at most one** valid owner — the requirement itself. This enforces consistency: you cannot satisfy a requirement with a different node at the same step.

### 3.2 `Reachable` — legal graph states

`Reachable reqOf` is an inductive predicate with three constructors:

```lean
inductive Reachable (reqOf : NodeId → List NodeId) : GPathM → Prop where
  | seed (d) (title)
      (hstep : d.step = 0)
      (hreqs_back : ∀ req ∈ reqOf d, req.step < d.step) :
      Reachable (initSeed d title)

  | up (g) (d) (title)
      (hstep : d.step = g.current_step)
      (hreqs_back : ∀ req ∈ reqOf d, req.step < d.step)
      (hreqs_distinct : ∀ r₁ r₂ ∈ reqOf d, r₁.step = r₂.step → r₁ = r₂) :
      Reachable g → Reachable (upFiltering g (reqOf d) d title)

  | join (g₁) (g₂) (hok : okJoin g₁ g₂) :
      Reachable g₁ → Reachable g₂ → Reachable (join g₁ g₂)
```

Each constructor carries the structural hypotheses that the concrete execution guarantees:

- **seed:** The root node is at step 0, and all its requirements point to earlier steps (forcing `reqOf d` to be empty or contain only negative-step nodes).
- **up:** The new node is at the current step (`d.step = g.current_step`), its requirements point strictly backward (`req.step < d.step`), and no two requirements share the same step (`r₁.step = r₂.step → r₁ = r₂`).
- **join:** The two graphs satisfy `okJoin` (same `current_step`, same `map_parent`, both valid).

### 3.3 Lemma L1

```lean
theorem L1 (h : Reachable reqOf g) : ReqFiltered reqOf g
```

**Proof structure** — induction on `Reachable`:

| Case | Strategy | Status |
|------|----------|--------|
| `seed` | Manually expands `initSeed`. The single node at step 0 has `owners = [pid]` where `pid.id.step = 0`. Since `req.step < 0` (from `hreqs_back`), the condition `q.id.step = req.step` is impossible. Closed via `omega`. | **Proved, no axioms** |
| `up` | `upFiltering = up (filterAll g reqs) d title`. If `filterAll` invalid, result is just the filtered graph (invariant holds by IH + A1). If valid, result is `addNode g' d title`. | **Rests on A1 and the false-as-stated A9** |
| `join` | Merges nodes by id; for each node in the result, either it comes from `g₁` (IH₁) or `g₂` (IH₂); merged nodes decompose via `mergeNode_owners_subset`; `node?_id_eq` transports `reqOf` across the id equality. | **Genuine 36-line case analysis; uses only A6/A7 (true, provable one-liners)** |

### 3.4 Lemma L1_cor

```lean
theorem L1_cor (h_reach : Reachable reqOf g)
    (h_chain : IsChain g sel) (h_owned : PairwiseOwned g sel)
    (j) (hj_lo : 0 ≤ j) (hj_hi : j < g.current_step)
    (req) (hreq : req ∈ reqOf (sel j).id)
    (h_req_step_pos : 0 ≤ req.step) (h_req_step_lt : req.step < g.current_step) :
    (sel req.step).id = req
```

**Proof structure** — case split on `req.step = j`; the equal case is refuted via `reqs_back_trans` (A3) + `chain_step_eq` (A8), the distinct case applies `PairwiseOwned` + `ReqFiltered`. **This theorem currently depends on the false axiom A8 and therefore proves nothing until `IsChain` is repaired** (after which A8 becomes a trivial lemma and the same proof text should go through).

---

## 4. Proof Status and Axiom Audit

### 4.0 Audit finding (2026-07-04): A8 makes the development inconsistent

`IsChain` requires only `(g.node? (sel k)).isSome` plus parent links; **nothing pins `(sel k).id.step` to `k`**. Countermodel: a graph whose single node lives at step 5 with `current_step = 1`, and `sel := fun _ => that node`. `IsChain` holds (the link clause is vacuous), yet A8 concludes `5 = 0`. The derivation was carried out in Lean against this codebase:

```
theorem inconsistent : False := ...
#print axioms inconsistent
-- 'inconsistent' depends on axioms: [propext, Quot.sound, chain_step_eq]
```

With `False` derivable, every proposition in scope of A8 is provable, so "0 `sorry`" carries no weight for anything downstream of it.

**A9 is also false as stated.** In `addNode_preserves_ReqFiltered`, `g'` is an auto-bound variable with **no connection to `g`**: the axiom claims that for *any* `ReqFiltered` graph `g'` and *any* reachable `g`, `addNode g' d title` preserves the invariant. Countermodel: `g' = { nodes := [], gowners := [q] }` with `q.id.step = req₀.step`, `q.id ≠ req₀` for some `req₀ ∈ reqOf d` — `ReqFiltered g'` holds vacuously, but the new node inherits `[q]` as owners and violates the invariant. The true statement requires `g' = filterAll g (reqOf d)` (which is how the axiom is *used*), because the filtering is what cleans `gowners`.

Both errors share one root: **the properties were axiomatized without the hypotheses that make them true.** An axiom never meets a type-checker for its truth; a proof does.

### 4.1 The "brecOn opacity" justification is incorrect

An earlier version of this document claimed that `|`-syntax definitions compile to `brecOn` and thereby block *all* reduction, making the axioms unavoidable. This is refuted **within this same repository**: `Fuel.lean` proves `measure_cleanInvalidGo_le`, `measure_reviewNode_le`, `measure_reviewSteps_le`, and `measure_reviewPass_le` — lemmas about exactly the functions listed as opaque — using `simp only [f]` (equation lemmas) plus `split`. The same technique, applied through the plan's `Pruned` relation, proves A1–A5. A6 and A7 are `List.mem_of_find?_eq_some` and `List.find?_some` + `beq_iff_eq`, both available in this toolchain (the pure model's `Axioms.lean` has used the same family for weeks). The axioms were a schedule shortcut, not a technical necessity.

### 4.2 The `OwnersSubset` bridge

```lean
def OwnersSubset (g g' : GPathM) : Prop :=
  ∀ d, d ∈ g'.nodes → ∃ d' ∈ g.nodes, d'.id = d.id ∧ ∀ q ∈ d.owners, q ∈ d'.owners

theorem OwnersSubset_preserves_ReqFiltered (h : ReqFiltered reqOf g)
    (hsub : OwnersSubset g g') : ReqFiltered reqOf g' := ...
```

This lemma (proved, no axioms) separates the structural property ("the operation only narrows owners or removes nodes") from the logical invariant. Once `OwnersSubset g g'` is established for an operation, invariant preservation follows automatically.

### 4.3 The nine axioms, audited

| # | Axiom | Verdict | Notes |
|---|-------|---------|-------|
| **A1** | `review_OwnersSubset` | True; provable | Induction over `reviewFuel` with per-op `Pruned` lemmas (same technique as `Fuel.lean`). |
| **A2** | `steps_below_current` | True; provable | Induction on `Reachable`; needs the `Pruned.step_eq` field for the pruning cases. |
| **A3** | `reqs_back_trans` | True; provable | Direct induction on `Reachable` (the `up` constructor carries exactly this hypothesis for the new node). |
| **A4** | `filterAll_mem_subset` | True; provable | `filterRequire` never touches nodes; `review` case is A1's walk. |
| **A5** | `filterAll_cleans_gowner` | True; provable | Fold lemma over `filterRequire` (the single-step version, T3, is already proved) + `review` only shrinks `gowners`. |
| **A6** | `node?_mem` | True; **one-liner** | `List.mem_of_find?_eq_some`. The earlier claim that it is unavailable in this Std4 version is wrong. |
| **A7** | `node?_id_eq` | True; **one-liner** | `List.find?_some` + `beq_iff_eq` (lawful `==` via `DecidableEq`). |
| **A8** | `chain_step_eq` | **FALSE — `False` derived** | See §4.0. Fix: add `(sel k).id.step = k` to `IsChain` (as the plan's F4 sketch specified); the axiom then becomes a trivial lemma. |
| **A9** | `addNode_preserves_ReqFiltered` | **FALSE as stated** | See §4.0. Fix: restate over `g' = filterAll g (reqOf d)` with the cleaned-gowners property (A5) and `pid_safe`; the plan's §7.2 L1.c is the full proof design. |

### 4.4 Proved without axioms

| Name | Statement | Proof method |
|------|-----------|-------------|
| `initSeed_ReqFiltered` | `ReqFiltered (initSeed d title)` | Manual expansion, single node at step 0, omega |
| `filterRequire_preserves_ReqFiltered` | `ReqFiltered g → ReqFiltered (filterRequire g req)` | `simp` — only `gowners` changes |
| `filterRequire_cleans_gowner` | Clean gowner for a single `filterRequire` | `List.mem_filter` decomposition |
| `OwnersSubset_preserves_ReqFiltered` | Bridge lemma | 4 lines, direct |
| `mergeNode_owners_subset` | `q ∈ mergeNode(a,b).owners → q ∈ a.owners ∨ q ∈ b.owners` | `List.mem_append` + `List.mem_filter` |
| `measure_reviewPass_le`, `review_stable` (F2) | Review-loop honesty | `simp only` + `split` over the `|`-defined functions |

---

## 5. Theorem Catalog

Axiom dependencies verified with `#print axioms` (2026-07-04):

| # | Theorem | Axioms in its closure | Evidential status |
|---|---------|----------------------|-------------------|
| T1 | `initSeed_ReqFiltered` | none | ✅ proved |
| T2 | `filterRequire_preserves_ReqFiltered` | none | ✅ proved |
| T3 | `filterRequire_cleans_gowner` | none | ✅ proved |
| T4 | `OwnersSubset_preserves_ReqFiltered` | none | ✅ proved |
| T5 | `filterAll_preserves_ReqFiltered` | A1 | conditional (A1 true, provable) |
| T6 | `mergeNode_owners_subset` | none | ✅ proved |
| T7 | `pid_safe` | A2, A3 | conditional (both true, provable) |
| T8 | `upFiltering_ReqFiltered` | A1, **A9** | ⛔ rests on a false axiom |
| T9 | `join_preserves_ReqFiltered` | A6, A7 | conditional (both one-liners) |
| **L1** | main theorem | A1, A6, A7, **A9** | ⛔ rests on a false axiom |
| **L1_cor** | chain owner identity | A1, A2, A3, A6, A7, **A8**, **A9** | ⛔ inconsistent context |

---

## 6. Repair Plan and Future Work

### 6.1 Repairing the phase (priority order)

1. **Fix `IsChain`**: add `(sel k).id.step = k` to the first clause. A8 then becomes a one-line lemma (or disappears into the hypothesis). `L1_cor`'s existing proof text should survive nearly unchanged.
2. **Restate and prove A9** over `g' = filterAll g (reqOf d)`, using A5 (cleaned gowners), `pid_safe`, and the `addNode` membership decomposition. The complete proof design is §7.2 (L1.c) of the plan.
3. **Replace A1–A5 with proofs** via the plan's `Pruned` relation (gowners-subset + node-derivation + step equality), reusing the `simp only [f]` + `split` technique already validated in `Fuel.lean`.
4. **Replace A6/A7** with their one-line proofs.
5. **Guard the standard**: add a CI check that fails if `#print axioms L1` reports any project axiom, restoring the invariant the project already achieved once for the pure model ("De los Axiomas a los Teoremas", chronicle v9).

After step 5, the F5 definition of done — *L1 and L1_cor with no `sorry` and no axioms* — is met.

### 6.2 Connecting to the executable (Lemma L7)

The `Reachable` predicate carries hypotheses (`hstep`, `hreqs_back`, `hreqs_distinct`, `hok`) that must be discharged by the concrete `AbsSat` execution driver, connecting executable semantics to the pure mirror.

### 6.3 Completing the denotation lemmas (L2–L6)

The `Denot.lean` module defines `IsChain`, `PairwiseOwned`, `pathOf`, and `denot` but provides only definitions. The remaining bridge phases (L2–L6 of `formal_bridge_owners_runpure.md`) must prove that these denotations are sound and complete with respect to the machine. L6 additionally needs F2.c (pass idempotence at the review fixpoint), which was deliberately deferred.

### 6.4 The differential harness (F6)

`MirrorTest.lean` + `lake exe diffTest` already validate the mirror empirically at scale (three bands, random instances, verdicts and full solution sets). Formalizing that equivalence for **all** inputs is a bisimulation proof between the two models — the ultimate goal of the bridge, distinct from and complementary to the randomized evidence.

---

*This document describes the Phase F5 work of July 2026 and incorporates the 2026-07-04 audit: the axiomatized shortcut is unsound as it stands, the architecture is right, and the road to an axiom-free L1 is fully mapped.*
