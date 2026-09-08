# Index of Formal Verification and Analysis Documents

This project contains a comprehensive suite of documents detailing the formal verification, complexity analysis, and mathematical foundations of the `AbsSat` algorithm implemented in Lean 4.

## Core Formal Verification
- [formal_verification.md](./formal_verification.md): High-level overview of the formal verification goals and model.
- [formal_verification_join.md](./formal_verification_join.md): Mathematical proof of the soundness and completeness of the `Join` operation.
- [formal_compression_strategy.md](./formal_compression_strategy.md): Analysis of the compression strategy and the Structural Boundedness Theorem.
- [formal_bridge_owners_runpure.md](./formal_bridge_owners_runpure.md): Design proposal (Spanish) for the missing bridge theorem — reading via Owners ≡ paths of `run_pure` — with the full correctness chain, lemma decomposition, and attack order.
- [../docs/summary_formalization.md](../docs/summary_formalization.md): **Phase F5 complete and axiom-free** — formal verification of the `ReqFiltered` invariant for `GPathM` and Lemma L1 (0 `sorry`, 0 project axioms; the closure of `L1`/`L1_cor` is `[propext, Quot.sound]`, pinned by build-failing `#guard_msgs`). Architecture, proof strategy, the 2026-07-04 audit that found axioms A8/A9 false, the 2026-07-05 repair, and the theorem catalog.

### Bridge phases (executable ↔ pure mirror)
Phases F1–F6 and lemma L1 are complete and axiom-free (see the summary above). Phase F2 — including F2.c in both its fixpoint and per-node forms — lives in `AbsSat/GraphPath/Model/Fuel.lean`. Bridge lemma L2's soundness and narrowing directions live in `AbsSat/GraphPath/Model/Filter.lean`; L3's soundness direction in `Model/Up.lean`; L4's monotone direction and L6's join case in `Model/Join.lean`; L6's statement, seed case and executable falsifier (`lake exe l6search`) in `Model/L6.lean` and `Model/L6Search.lean`, and its `up` case reduced to the review step in `Model/L6Up.lean`. What remains open is a single statement — `SupportedG g → SupportedG (review g)` — which is simultaneously L6's last case, L2's ⊇ direction and L3's ⊇ direction. Execution log: [../docs/plans/espejo_gpathm_lema_L1.md](../docs/plans/espejo_gpathm_lema_L1.md).

## Complexity and Performance
- [complexity.md](./complexity.md): Detailed asymptotic analysis of time and space complexity ($O(S^4)$).

## Narrative and Author Support (Spanish)
- [verificacion_narrativa_es.md](./verificacion_narrativa_es.md): Narrative explanation of the verification process in Spanish.
- [verification_inseguridad_autor_main.md](./verification_inseguridad_autor_main.md): Human-AI collaboration summary and publication recommendation.

### Sequential Reassurance Documents
- [v1: El Algoritmo es Sólido](./verificacion_inseguridad_autor.md)
- [v2: Matemáticas vs Incertidumbre](./verificacion_inseguridad_autor_v2.md)
- [v3: Join es una Unión Segura](./verificacion_inseguridad_autor_v3.md)
- [v4: La Batalla por la Complejidad](./verificacion_inseguridad_autor_v4.md)
- [v5: La Victoria Estructural](./verificacion_inseguridad_autor_v5.md)
- [v6: Reflexión Personal (Gemini)](./verificacion_inseguridad_autor_v6.md)
- [v7: Coherencia del O(S^4)](./verificacion_inseguridad_autor_v7.md)
- [v8: El Abogado del Diablo](./verificacion_inseguridad_autor_v8.md)
- [v9: De los Axiomas a los Teoremas (Claude)](./verificacion_inseguridad_autor_v9.md)
- [v10: Lo que las pruebas dicen sobre el algoritmo (Claude)](./verificacion_inseguridad_autor_v10.md) — qué son realmente los `owners`, las tres invariantes de una cadena y por qué los rangos de las pasadas de coherencia cargan con la demostración. **Su §1 está corregida por v11.**
- [v11: Dónde está de verdad el problema de Helly (Claude)](./verificacion_inseguridad_autor_v11.md) — corrige v10: L6 son dos enunciados (preservación y "sin zombis"), solo el segundo necesita la estructura 3SAT, y es el que sostiene la soundness de los veredictos.

---
*Created by Gemini (Antigravity/Jules) in collaboration with Deepseek, Claude (Sonnet 5), and the Author.*
