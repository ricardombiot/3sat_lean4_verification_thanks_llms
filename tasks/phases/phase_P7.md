# Plantilla de Fase de Proyecto

**PHASE ID:** P7

**PHASE NAME:** SatMachine y verificaciones

**OBJECTIVES:**
- Migrar los módulos `SatMachine` y `SatMachinePow` que implementan el solver SAT.
- Migrar las utilidades de verificación (`checker.jl`, `exaustive_solver.jl`).
- Verificar la correctitud del algoritmo de resolución SAT (relación entre el grafo y las soluciones).

**DELIVERABLES:**
- Módulo Lean `AbsSat.SatMachine` equivalente a `sat_machine.jl`.
- Módulo Lean `AbsSat.SatMachinePow` equivalente a `sat_machine_pow.jl`.
- Módulo Lean `AbsSat.CheckerCnf` equivalente a `checker.jl`.
- Módulo Lean `AbsSat.ExhaustiveSolver` equivalente a `exaustive_solver.jl`.
- Teoremas que relacionan las soluciones encontradas por `SatMachine` con la satisfacibilidad de la fórmula CNF.
- Tests integrales que validan el flujo completo (importar CNF, construir grafo, ejecutar solver, verificar solución).

**SUCCESS CRITERIA:**
1. `SatMachine` y `SatMachinePow` están implementados y pueden resolver instancias CNF simples.
2. El `CheckerCnf` puede verificar soluciones contra la fórmula original.
3. El `ExhaustiveSolver` (opcional) proporciona una referencia para contrastar con el solver principal.
4. Se demuestra formalmente que si `SatMachine` reporta una solución, esa solución satisface la fórmula CNF.
5. El código compila y los tests pasan.

**MICROTASKS:**
0051, 0052, 0053, 0054, 0055, 0056, 0057, 0061, 0062, 0063, 0064, 0065
**DEPENDENCIES:**
P3 (GraphMap), P5 (GraphPath avanzado), P6 (GraphPow)

**RISKS & MITIGATIONS:**
- **Riesgo**: La correctitud del solver es compleja de verificar (equivalencia entre el grafo y la fórmula).
  **Mitigación**: Enfocarse primero en probar la correspondencia paso a paso y usar lemas ya verificados de fases anteriores.
- **Riesgo**: `SatMachinePow` es una versión optimizada que puede ser más difícil de analizar.
  **Mitigación**: Verificar primero `SatMachine` básico y luego extender a `SatMachinePow` reutilizando las mismas propiedades.
- **Riesgo**: La verificación formal de que el solver encuentra todas las soluciones (completitud) puede ser muy exigente.
  **Mitigación**: Priorizar la verificación de correctitud (si encuentra una solución, es válida) y posponer la completitud.

---

**NOTES:**
- Referencia: `docs/original_julia/src/sat_machine/` y `docs/original_julia/src/utils/checker.jl`, `exaustive_solver.jl`.
- Esta fase integra todos los componentes previos y constituye el objetivo final del proyecto.
- La verificación de correctitud parcial (soundness) ya sería un hito significativo.
