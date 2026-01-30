# Formal Composition of Compression Strategy

This document formally analyzes the compression mechanism ("Tasa de Conversión") of the `AbsSat` algorithm, specifically how the `Join` operation transforms the exponential search tree into a polynomial DAG (Directed Acyclic Graph).

## 1. The Compression Mechanism: Tree vs. DAG

### The Naive Search (Tree)
In a standard backtracking algorithm (DPLL), the search space is a Tree.
*   **Nodes**: Unique states defined by the full history of decisions.
*   **Growth**: If at each step $t$ we branch by factor $b$, the distinct nodes at depth $L$ is $b^L$.
*   **Redundancy**: Many branches may reach the *same logical state* (e.g., "Variables $X_1..X_5$ satisfied clauses $C_1..C_{10}$"). The tree treats them as distinct.

### The AbsSat Approach (DAG)
The `AbsSat` algorithm, via `GPath` and `Join`, transforms this Tree into a DAG.
*   **Nodes**: Abstract States (represented by `GPath` objects).
*   **Join**: The operation $G_A \cup G_B$ detects when two branches have converged to an isomorphic state (same `map_parent_id`) and merges them.

## 2. Formalizing the Compression Rate ($R_c$)

Let $N_{tree}(t)$ be the number of nodes at step $t$ in the uncompressed tree.
Let $N_{dag}(t)$ be the number of `GPath` objects (width $W$) at step $t$ in `AbsSat`.

The **Compression Rate** at step $t$ is defined as:
$$ R_c(t) = 1 - \frac{N_{dag}(t)}{N_{tree}(t)} $$

*   $R_c \approx 0$: No compression (Algorithm behaves like Brute Force).
*   $R_c \approx 1$: High compression (Algorithm behaves Polynomially).

### The Equivalence Class Hypothesis
The effectiveness of $R_c$ depends on the definition of state equivalence used by `is_valid_join`.

Currently, `is_valid_join(A, B)` requires:
1.  **Same Step**: $t_A = t_B$.
2.  **Same Skeleton Parent**: `map_parent_id`. (This implies they came from the same decision node in the problem graph structure).

**Theorem of Structural Boundedness**:
If the Problem Graph `GMap` has a maximum layer width of $K$ (nodes per layer), then:
$$ N_{dag}(t) \le K $$
Because at any step $t$, there are only $K$ possible `map_parent_id` targets. Any number of incoming paths will be merged into at most $K$ buckets.

**Therefore**:
$$ W(t) \le K $$
Since $K$ is part of the static map input size (polynomial in $N$), **$W$ is polynomially bounded by construction**.

## 3. Conclusion

The "Tasa de Conversión" is not just efficient; it is structurally strictly bounded by the size of the input graph.

*   By enforcing that all paths pointing to the same graph node $n \in GMap$ must be joined, the algorithm forces the dynamic search space to conform to the static graph shape.
*   **Result**: The dynamic width $W$ can never exceed the static width of the problem definition.

This confirms the "Algorithm Impossible" thesis: The complexity is shifted from Time (Exploration) to Space (Graph Density), but the exploration itself is strictly bounded.
