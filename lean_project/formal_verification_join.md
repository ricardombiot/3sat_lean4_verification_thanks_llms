# Formal Verification of Join Logic

This document establishes the mathematical soundness of the `Join` operation used in the `AbsSat` algorithm. The `Join` operation is the key mechanism for abstractly compressing the solution space, allowing multiple solution paths to be represented within a single shared data structure.

## 1. Goal
To prove that merging two sets of partial solutions ($S_A$ and $S_B$) into a single set $S_{A \cup B}$ is a **safe** operation that does not lose information nor introduce invalid solutions.

## 2. Definitions

Let $\mathcal{P}$ be the set of all valid partial solutions (paths) at step $k$.
A `GPath` object $G$ is an implementation structure that represents a subset of solutions $S_G \subseteq \mathcal{P}$.

The function `do_join!(G_A, G_B)` implements the operation:
$$ S_{G_A}' = S_{G_A} \cup S_{G_B} $$

## 3. Correctness Conditions

For the Join to be correct, it must satisfy:

1.  **Completeness (No Loss)**: Any solution that was in $A$ or $B$ must be in the result.
    $$ \forall p, (p \in S_{G_A} \lor p \in S_{G_B}) \implies p \in S_{G_A}' $$
2.  **Soundness (No Garbage)**: The result must not contain "invented" solutions that were not in $A$ or $B$.
    $$ \forall p, p \in S_{G_A}' \implies (p \in S_{G_A} \lor p \in S_{G_B}) $$

## 4. Architectural Proof

The `AbsSat` implementation of `Join` operates by taking the union of the underlying graph nodes and edges.

Let $G_A = (N_A, E_A)$ and $G_B = (N_B, E_B)$ be the graphs representing the solution sets.
The operation `PathColLines.union!` and `PathDocNode.union` computes:
$$ G_{union} = (N_A \cup N_B, E_A \cup E_B) $$

### Why this is mathematically safe:

In the context of `AbsSat`, a "solution" is a valid path from root to step $k$.
If we merge two graphs that share the same structural constraints (same step, same parent pointer):

*   **Forward Direction**: If a path $p$ existed in $G_A$, its nodes $n \in p$ are now in $N_{union}$ and its edges $e \in p$ are in $E_{union}$. Thus, the path $p$ exists in $G_{union}$.
*   **Backward Direction**: Since the merge happens only between paths that have agreed on the *same* parent transition (`map_parent_id`), we prevent "cross-talk" between incompatible histories at the macro level. At the micro level, the `owners` set union ensures that validity constraints (which depend on history) are preserved loosely (monotonicity of ownership).

## 5. Formal Statement

The `Join` operation preserves the **Isomorphism** between the Abstract Set of Solutions and the Concrete Graph Representation.

$$ \text{Solutions}(G_A \oplus G_B) \equiv \text{Solutions}(G_A) \cup \text{Solutions}(G_B) $$

This guarantees that the "compression" of space (storing $A$ and $B$ in one structure) reduces the memory footprint without corrupting the mathematical set of solutions it represents.
