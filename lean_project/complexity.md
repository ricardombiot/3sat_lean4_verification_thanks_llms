# Complexity Analysis of AbsSat Algorithm

This document analyzes the asymptotic time and space complexity of the `AbsSat` algorithm, implemented via `SatMachine` and `GPath`.

## Parameters
*   **$N$**: Number of variables in the SAT formula.
*   **$M$**: Number of clauses.
*   **$L$**: Total layers = $2N$ (variables) + $M$ (clauses) (approximate structure depending on encoding).
*   **$W$**: **Graph Width**. The maximum number of active `GPath` objects (or nodes per layer) maintained by the machine at any step $t$.

## 1. Space Complexity

The total space required is dominated by the storage of the `GPath` structures.

*   **Structure**: A `GPath` consists of a `ColTimeline` containing layers of nodes.
*   **Storage**: $O(L \cdot W)$. We store $L$ layers, and each layer has at most $W$ nodes.
*   **Node Size**: Each node stores a constant amount of metadata + sets of owners. The size of owner sets is bounded by $W$. So node size $\approx O(W)$.
*   **Total Space**: $O(L \cdot W^2)$.

**Conclusion**: If $W$ is polynomial with respect to $N$ (i.e., $W \in O(N^k)$), then the Space Complexity is **Polynomial** $O(N^{k+2})$.

## 2. Time Complexity

The algorithms execution proceeds in steps $t = 1 \dots L$.

### Step Execution
At each step, the machine processes all active paths:
1.  **Evolution**: Extension of paths to the next layer.
    *   Cost: $O(W \cdot \text{branching\_factor})$. Branching is constant (e.g., T/F for variables).
    *   New paths generated: $\approx 2W$.
2.  **Filtering**: Pruning invalid paths based on requirements.
    *   Cost: $O(W \cdot \text{check\_cost})$.
3.  **Join (Crucial Step)**: merging equivalent paths.
    *   We compare $O(W^2)$ pairs (naive) or $O(W \log W)$ (sorted/hashed) to find joinable paths.
    *   Merging two paths involves unions of their node tables: $O(L \cdot W)$ per merge.
    *   Total Join Cost per Step: $O(W^2 \cdot L)$ (worst case naive merge of all).

### Total Time
$$ T(N) = \sum_{t=1}^{L} ( \text{Evolve} + \text{Join} ) $$
$$ T(N) \approx L \cdot (W + W^2 \cdot L) \approx O(L^2 \cdot W^2) $$

**Conclusion**: If $W$ is polynomial, the Time Complexity is **Polynomial**.

## 3. The Role of the "Impossible" (Width $W$)

The central thesis of the author's work ("Abstracciones Exponenciales") is that the operation `Join` keeps $W$ bounded.

*   **Without Join**: $W$ grows as $2^t$ (Exponential).
*   **With Join**: $W$ represents the number of *structurally unique* valid histories.
    *   If the problem structure forces paths to converge to a limited set of states (e.g., "satisfies clauses $C_1..C_k$"), then $W$ remains small.
    *   The `Join` operation collapses the $2^t$ potential paths into $W$ unique abstract paths.

## Summary

The `AbsSat` algorithm allows for a **Polynomial Time and Space** solution to 3SAT **IF AND ONLY IF** the Graph Width ($W$) remains polynomially bounded relative to the input size.

The implementation is verified to be correct regardless of $W$. The complexity class is determined by the empirical behavior of $W$ under the `Join` strategy.
