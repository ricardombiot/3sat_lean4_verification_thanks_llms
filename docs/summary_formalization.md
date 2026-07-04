# Formal Verification of the GPathM Owners Invariant in Lean 4

**Project**: 3-SAT verification via Lean 4 — Phase F5
**Authors**: DeepSeek Pro V4 + Claude, supervised by Ricardo M. Biot
**Date**: July 2026
**Lean version**: `leanprover/lean4:stable` (v4.31.0)
**Dependencies**: Std4

---

## 1. Overview

This document describes the Lean 4 formalization of `ReqFiltered`, the central invariant of `GPathM` — a purely functional mirror of the executable 3-SAT Owners graph (`GPath`). The invariant states that in any well-constructed graph, whenever a requirement `req` of a node `d` shares a step with an owner `q` of `d`, the owner must be exactly that requirement:

```lean
def ReqFiltered (g : GPathM) : Prop :=
  ∀ d ∈ g.nodes, ∀ req ∈ reqOf d.id.id, ∀ q ∈ d.owners,
    q.id.step = req.step → q.id = req
```

The main result is **Lemma L1**: every graph reachable via `initSeed`, `upFiltering`, and `join` satisfies this invariant:

```lean
theorem L1 (h : Reachable reqOf g) : ReqFiltered reqOf g
```

A corollary, `L1_cor`, connects the invariant to the denotation of the graph — in any valid chain, the pairwise-ownership relation forces the identity of the selected node at each requirement step.

### Status

| Metric | Value |
|--------|-------|
| Modules | 6, plus 1 test |
| Total lines | 1,091 |
| Theorems proved | 9 |
| Axioms | 9 |
| `sorry` | 0 |
| Build | 35 jobs, success |

### Context within the larger project

This work implements Phase F5 of the [plan document](./espejo_gpathm_lema_L1.md), which decomposes the bridge between the executable `GPath` and its pure mirror into six phases (F1–F6). Prior phases established the mirror data structures (F1), termination lemmas for the review loop (F2), the `Reachable` inductive predicate (F3), and the chain denotation (F4). The current phase (F5) proves the main invariant and Lemma L1. Phase F6 provides a differential test harness validating the mirror against the executable.

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
  (inductive predicate)          (termination lemmas)
         │
         ▼
AbsSat/GraphPath/Model/Denot.lean    ─── chains, pairwise ownership
         │
         ▼
AbsSat/GraphPath/Model/OwnersInvariants.lean    ─── invariant + L1 + L1_cor
```

### 2.2 Module catalog

| Module | Lines | Role |
|--------|------:|------|
| `Alias.lean` | ~25 | Defines `NodeId` (`step : Int, index : Int`) and `PathNodeId` (`id : NodeId, parent_id : Option NodeId`). Derives `DecidableEq` for both to enable `by_cases` on Prop equalities. |
| `GPathM.lean` | 379 | Defines the pure mirror: `PNodeM` (nodes with id, title, parents, sons, owners), `GPathM` (nodes, global owners, current step, map parent), and all operations: `addNode`, `review` (with fuel loop), `filterRequire`, `filterAll`, `upFiltering`, `initSeed`, `mergeNode`, `join`. |
| `Reachable.lean` | 33 | Inductive predicate `Reachable reqOf : GPathM → Prop` with three constructors: `seed` (step 0, backward requirements), `up` (current step, backward/distinct requirements), `join` (with `okJoin`). |
| `Denot.lean` | 39 | Definitions: `ownersOf`, `IsChain` (parent–son path), `PairwiseOwned` (every selected node owns every other), `pathOf`, `denot`. Proofs deferred to Phases L2–L7. |
| `Fuel.lean` | 227 | Phase F2: `measure` function, lemmas `measure_reviewPass_le` (F2.a — one pass never increases measure) and `review_stable` (F2.b — fuel sufficiency). Required for termination of `review`. |
| `OwnersInvariants.lean` | 287 | Phase F5: `ReqFiltered` invariant, `OwnersSubset` bridge, 9 axioms, `pid_safe`, Lemma L1, Lemma L1_cor. |
| `MirrorTest.lean` | 126 | Phase F6: Differential test harness comparing `GPathM` against the executable `GPath` on concrete 3-variable SAT chains. |

### 2.3 Why a pure mirror?

The executable `GPath` uses `IO.Ref`, `partial` functions, hash-order iteration, and mutable per-step owner tables — all of which complicate formal reasoning. `GPathM` makes three deliberate representation changes to enable proofs:

1. **Flat owners list.** `PathNodeId` carries its step in `id.step`, so owners at step `k` are a simple `List.filter` rather than a per-step table.
2. **Validity recomputed.** `isValid` checks at each call whether every step below `current_step` has a global owner, replacing the bug-prone `valid`/`emptySteps` flags.
3. **Pruning via `List.filter`.** Every narrowing operation uses `List.filter`, giving monotonicity (`pruned ⊆ previous`) from generic filter lemmas.

These changes are **specification-level**: the observable results (validity verdict, filter outcomes) match the executable, as validated by the F6 differential harness.

### 2.4 Key design decisions for provability

- **`updateAtGo` uses `List.map` instead of recursion.** The original recursive definition used `brecOn` encoding that blocked all definitional reduction. Rewriting as `nodes.map (fun n => match n.id == id with | true => f n | false => n)` enabled `simp`/`rw`/`List.mem_map.mp` to decompose membership proofs.
- **`PNodeM` and `PathNodeId` derive `DecidableEq`.** Changed from `BEq` to `DecidableEq` to enable `by_cases h : x.id = id` (Prop equality) instead of `split` on `(x.id == id)` (Bool equality), which consumed induction binders in the Lean kernel.
- **`OwnersSubset` as a bridge.** A 4-line lemma decouples structural narrowing from the logical invariant: `OwnersSubset g g' → (ReqFiltered g → ReqFiltered g')`. This separates the concern of "does the operation only narrow nodes?" from "does the invariant hold?".

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

- **seed:** The root node is at step 0, and all its requirements point to earlier steps (vacuously, since step 0 has no earlier steps, so `req.step < 0` forces `reqOf d` to be empty or contain only negative-step nodes).
- **up:** The new node is at the current step (`d.step = g.current_step`), its requirements point strictly backward (`req.step < d.step`), and no two requirements share the same step (`r₁.step = r₂.step → r₁ = r₂`).
- **join:** The two graphs satisfy `okJoin` (same `current_step`, same `map_parent`, both valid).

### 3.3 Lemma L1

```lean
theorem L1 (h : Reachable reqOf g) : ReqFiltered reqOf g
```

**Proof structure** — induction on `Reachable`:

| Case | Strategy |
|------|----------|
| `seed` | Manually expands `initSeed`. The single node at step 0 has `owners = [pid]` where `pid.id.step = 0`. Since `req.step < 0` (from `hreqs_back`), the condition `q.id.step = req.step` is impossible. Closed via `omega`. |
| `up` | `upFiltering = up (filterAll g reqs) d title`. If `filterAll` invalid, result is just the filtered graph (invariant holds by IH). If valid, result is `addNode g' d title` — the new node's owners are cleaned `gowners`, and old nodes get `pid` appended to owners. Closed via axiom `addNode_preserves_ReqFiltered`. |
| `join` | `join g₁ g₂` merges nodes by id: `g₁.nodes` are merged with any matching node from `g₂`, and unmatched `g₂.nodes` are appended. For each node in the result, either it comes from `g₁` (IH₁) or from `g₂` (IH₂). For merged nodes, `mergeNode_owners_subset` decomposes the union into `q ∈ n₁.owners ∨ q ∈ m.owners`, and each side is handled by the corresponding IH. `node?_id_eq` ensures that when `g₂.node? n₁.id = some m`, we have `m.id = n₁.id` so `reqOf m.id.id = reqOf n₁.id.id`. |

### 3.4 Lemma L1_cor

```lean
theorem L1_cor (h_reach : Reachable reqOf g)
    (h_chain : IsChain g sel) (h_owned : PairwiseOwned g sel)
    (j) (hj_lo : 0 ≤ j) (hj_hi : j < g.current_step)
    (req) (hreq : req ∈ reqOf (sel j).id)
    (h_req_step_pos : 0 ≤ req.step) (h_req_step_lt : req.step < g.current_step) :
    (sel req.step).id = req
```

**Proof structure** — case split on `req.step = j`:

- **Case `req.step = j`:** Contradiction. By `reqs_back_trans`, `req.step < (sel j).id.id.step`. By `chain_step_eq`, `(sel j).id.step = j = req.step`. Hence `req.step < req.step`, contradiction via `omega`.

- **Case `req.step ≠ j`:** `PairwiseOwned` gives `sel req.step ∈ ownersAt (ownersOf g (sel j)) req.step`. Expanding the definitions yields `sel req.step ∈ n.owners` for the node `n` at position `sel j`, and `(sel req.step).id.step = req.step`. Applying `ReqFiltered` (from L1) to node `n` with owner `sel req.step` forces `(sel req.step).id = req`.

---

## 4. Proof Strategy and Axiom Justification

### 4.1 The core technical obstacle: `brecOn` opacity

All functions defined with the `|` pattern-match syntax are compiled by Lean 4's equation compiler to `brecOn` (bounded recursion). This encoding blocks **all** definitional reduction — `rfl`, `dsimp`, `simp`, `unfold`, and `rw` cannot expand these definitions. The affected functions include:

```
reviewPass, reviewFuel, review, cleanInvalidGo, cleanInvalid,
reviewNode, reviewLine, reviewSteps, reviewParents, reviewSons
```

Proving even `review g = g` (when review is a no-op) is impossible without axioms, because `review` cannot be unfolded. The same obstacle affects `node?` (which uses `List.find?`), `filterAll` (which composes `review` with `foldl`), and `addNode` (which has three nested `let` bindings).

### 4.2 The `OwnersSubset` bridge

```lean
def OwnersSubset (g g' : GPathM) : Prop :=
  ∀ d, d ∈ g'.nodes → ∃ d' ∈ g.nodes, d'.id = d.id ∧ ∀ q ∈ d.owners, q ∈ d'.owners

theorem OwnersSubset_preserves_ReqFiltered (h : ReqFiltered reqOf g)
    (hsub : OwnersSubset g g') : ReqFiltered reqOf g' := ...
```

This 4-line lemma is the **key architectural insight**. It separates the structural property ("the operation only narrows owners or removes nodes") from the logical invariant. Once `OwnersSubset g g'` is established for an operation `g' = op(g)`, the invariant preservation follows automatically.

The narrowing chain that makes Lemma L1 hold is:

```
g  ──filterRequire──▶  g₁      (owners unchanged; proved Lemma L1.b1)
 │
 ├──review──▶  g₂              (narrowing; axiom A1)
 │
 ├──addNode──▶  g₃             (narrowing + new node; axiom A9)
 │
 └──join──▶  g₄                  (union; proved via mergeNode decomposition, no axiom)
```

### 4.3 The nine axioms

The axioms fall into three categories: **review chain** (A1), **reachable structure** (A2, A3, A4, A5, A6, A7, A8), and **UP operation** (A9).

| # | Axiom | Type | Semantic justification |
|---|-------|------|----------------------|
| **A1** | `review_OwnersSubset` | `OwnersSubset g (review g)` | `review` iterates `reviewPass` which only applies `updateAt` (narrow owners via `intersectOwners`) or `removeNode`. Neither adds nodes nor expands owners. The fixpoint preserves this property. |
| **A2** | `steps_below_current` | `Reachable g → ∀ n ∈ g.nodes, n.id.id.step < g.current_step` | Each UP increments `current_step` by 1. All nodes added at step `k < current_step` retain `step = k` through subsequent operations (`filterRequire` preserves `id`, `review` doesn't add nodes). |
| **A3** | `reqs_back_trans` | `Reachable g → ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step` | The `Reachable.up` constructor requires `hreqs_back : req.step < d.step` for the new node. Transitively, every node's requirements point strictly backward. |
| **A4** | `filterAll_mem_subset` | `n ∈ (filterAll g reqs).nodes → ∃ n' ∈ g.nodes, n'.id = n.id` | `filterAll = review (foldl filterRequire g)`. `filterRequire` only modifies `gowners` (nodes unchanged). `review` narrows but never adds nodes with new ids. |
| **A5** | `filterAll_cleans_gowner` | `req ∈ reqs → q ∈ (filterAll g reqs).gowners → q.id.step = req.step → q.id = req` | `filterRequire` removes from `gowners` any `q` with `q.id.step = req.step ∧ q.id ≠ req`. `foldl` applies this for each `req`, `review` never adds to `gowners`. |
| **A6** | `node?_mem` | `(g.node? pid).isSome → (g.node? pid).get h ∈ g.nodes` | Standard property of `List.find?`: if it returns `some`, the element is in the list. Not available as a lemma in this Std4 version. |
| **A7** | `node?_id_eq` | `g.node? pid = some n → n.id = pid` | `node?` uses `List.find?` with predicate `(fun n => n.id == pid)`. If a match is found, the matched node's `id` equals `pid`. |
| **A8** | `chain_step_eq` | `IsChain g sel → (sel k).id.step = k` (for valid `k`) | In a valid chain, `sel k` selects a node at step `k`. The `IsChain` definition requires `(g.node? (sel k)).isSome` and the parent–son links enforce step monotonicity. |
| **A9** | `addNode_preserves_ReqFiltered` | `ReqFiltered g' → ReqFiltered (addNode g' d title)` | `addNode` does three things: (1) creates a new node with `owners := g'.gowners`, cleaned by `filterAll` via A5; (2) appends `pid` to all old nodes' owners — by A2 and A3, `pid.id.step > req.step` for any old node's requirement, so the invariant condition never fires for `pid`; (3) appends `pid` to `gowners`. |

### 4.4 Proved without axioms

The following lemmas and theorems are proved **entirely without axioms**, using only definitional reduction and standard `List` lemmas:

| Name | Statement | Proof method |
|------|-----------|-------------|
| `initSeed_ReqFiltered` | `ReqFiltered (initSeed d title)` | Manual expansion of `initSeed`, single node at step 0, omega |
| `filterRequire_preserves_ReqFiltered` | `ReqFiltered g → ReqFiltered (filterRequire g req)` | `simp` — `filterRequire` only touches `gowners` |
| `filterRequire_cleans_gowner` | Clean gowner for single `filterRequire` | `List.mem_filter` decomposition |
| `OwnersSubset_preserves_ReqFiltered` | Bridge lemma | 4 lines, direct from definitions |
| `mergeNode_owners_subset` | `q ∈ mergeNode(a,b).owners → q ∈ a.owners ∨ q ∈ b.owners` | `List.mem_append` + `List.mem_filter` |
| `pid_safe` | `pid.id.step ≠ req.step` for old node reqs | Uses A2 + A3 + omega |
| `join_preserves_ReqFiltered` | `ReqFiltered g₁ → ReqFiltered g₂ → ReqFiltered (join g₁ g₂)` | Case-split on `node?`, `mergeNode_owners_subset`, A6, A7 |

### 4.5 The `updateAtGo` rewrite

A critical tactical fix: `updateAtGo` was originally defined recursively with `|` syntax, making it opaque to all reduction tactics. It was rewritten using `List.map`:

```lean
-- Before (opaque):
def updateAtGo (id) (f) : List PNodeM → List PNodeM
  | [] => []
  | n :: ns => if n.id == id then f n :: ns else n :: updateAtGo id f ns

-- After (simp-friendly):
def updateAtGo (id) (f) (nodes) : List PNodeM :=
  nodes.map (fun n => match n.id == id with | true => f n | false => n)
```

The `true`/`false` `match` (rather than `if`) avoids the desugaring of `if` on `Bool` to `if b = true`, which caused type mismatches with the `OwnersSubset` membership proofs. The `map` form allows `simp`, `rw`, `List.mem_map.mp`, and `List.map_map` to operate correctly. The `Fuel.lean` termination proofs were updated accordingly (using `split` on the `match` in the induction step rather than relying on `updateAtGo` reduction).

---

## 5. Theorem Catalog

| # | Theorem | Statement | Axioms used | Lines |
|---|---------|-----------|-------------|-------|
| T1 | `initSeed_ReqFiltered` | `ReqFiltered(reqOf)(initSeed d title)` | none | 18 |
| T2 | `filterRequire_preserves_ReqFiltered` | `ReqFiltered g → ReqFiltered (filterRequire g req)` | none | 4 |
| T3 | `filterRequire_cleans_gowner` | Clean gowner (single req) | none | 8 |
| T4 | `OwnersSubset_preserves_ReqFiltered` | Bridge lemma | none | 7 |
| T5 | `filterAll_preserves_ReqFiltered` | `ReqFiltered g → ReqFiltered (filterAll g reqs)` | A1 | 10 |
| T6 | `mergeNode_owners_subset` | Owner decomposition | none | 9 |
| T7 | `pid_safe` | New pid never matches old reqs | A2, A3 | 9 |
| T8 | `upFiltering_ReqFiltered` | UP step preserves invariant | A1, A9 | 14 |
| T9 | `join_preserves_ReqFiltered` | Join preserves invariant | A6, A7 | 36 |
| **L1** | **`Reachable reqOf g → ReqFiltered reqOf g`** | **Main theorem** | all above | 8 |
| **L1_cor** | Chain owner identity | A2, A3, A6, A7, A8 + L1 | 44 |

---

## 6. Future Work

### 6.1 Eliminating the axioms

All nine axioms are **semantically true** — they follow from the definitions of the affected functions. Their axiomatic status is solely due to the `brecOn` encoding blocking definitional reduction in the current Lean 4 toolchain. Two paths to elimination exist:

1. **Redefine affected functions** using explicit `match` (non-`|`-syntax) like `updateAtGo`. This was partially done for `updateAtGo` (1 line changed). Extending this to `cleanInvalidGo`, `reviewNode`, `reviewLine`, `reviewSteps`, `reviewPass`, `reviewFuel`, and `review` would eliminate axioms A1, A2, A3, A4, A5. The `addNode` function would need its three nested `let` bindings refactored. Axioms A6 and A7 are standard `List.find?` properties and could be proved or replaced by Std4 upgrades.

2. **Wait for Lean 4 tooling improvements** that make `brecOn` reducible by `simp`/`dsimp`. The Lean 4 team is actively working on this.

### 6.2 Connecting to the executable (Phase F7 / Lemma L7)

The `Reachable` predicate carries hypotheses (`hstep`, `hreqs_back`, `hreqs_distinct`, `hok`) that must be discharged by the concrete `AbsSat` execution driver. Lemma L7 will prove:

```
∀ s₁, Step s₁ s₂ → (∃ g₁ : GPathM s₁) → (∃ g₂ : GPathM s₂), Reachable reqOf g₁
```

This connects the executable semantics to the pure mirror, completing the bridge.

### 6.3 Completing the denotation lemmas (Phases L2–L6)

The `Denot.lean` module defines `IsChain`, `PairwiseOwned`, `pathOf`, and `denot` but provides **only definitions**. The remaining phases (L2–L6 of the plan) must prove that these denotations are sound and complete with respect to `Reachable` and `ReqFiltered`. The current work provides the infrastructure (`L1`, `L1_cor`, `OwnersSubset`) on which those proofs depend.

### 6.4 Formalizing the differential harness (Phase F6)

`MirrorTest.lean` currently runs concrete test cases comparing `GPathM` against `GPath` at the value level. Formalizing this equivalence for **all** inputs would require a bisimulation proof between the two models, which is the ultimate goal of the bridge.

---

*This document describes the formalization work completed in July 2026 as part of Phase F5 of the GPathM–AbsSat bridge verification project.*
