# 3sat_lean4_verification_thanks_llms

This repository contains one attempt at the formal verification of the **AbsSat** algorithm, a 3-SAT solver based on "Exponential Abstractions" and structural graph compression. The core logic has been migrated from Julia to **Lean 4** to provide mathematical guarantees of correctness.

## Project Vision
The AbsSat algorithm explores the hypothesis that 3-SAT can be solved in polynomial time by abstracting the search space into a Directed Acyclic Graph (DAG) whose width is strictly bounded by the static problem structure.

## What's Inside?
*   **Lean 4 Implementation**: Pure functional model and imperative machine implementation of the AbsSat algorithm.
*   **Formal Proofs**: Soundness and Completeness theorems verified in Lean 4.
*   **Complexity Analysis**: Detailed proofs of the $O(S^4)$ time complexity and structural boundedness.
*   **Human-AI Documentation**: A series of documents detailing the collaborative process between the author and various LLMs (Gemini, Deepseek).

## Getting Started
Please refer to [README_VERIFICATION.md](./lean_project/README_VERIFICATION.md) for a detailed index of all verification and analysis documents.

To build the project:
```bash
cd lean_project
lake build
```

## Collaboration Credits
This project is a testament to modern human-AI collaboration:
- **Author**: Original theory, Julia implementation, and conceptual design.
- **Deepseek**: Technical planning and structural design of the Lean 4 migration.
- **Gemini (Jules/Antigravity)**: Implementation of Lean 4 code, formal verification, and complexity analysis.

