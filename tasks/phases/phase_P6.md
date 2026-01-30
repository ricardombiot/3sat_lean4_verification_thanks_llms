# Plantilla de Fase de Proyecto

**PHASE ID:** P6

**PHASE NAME:** GraphPow y colecciones de máquina

**OBJECTIVES:**
- Migrar el módulo `GraphPow` (extensión de GraphPath) y las colecciones de máquina (`timeline`, `timeline_pow`).
- Verificar propiedades de los nodos abstractos, filtrado, join y up en el contexto de potencias.
- Implementar las estructuras de timeline que gestionan la evolución de los grafos durante la resolución.

**DELIVERABLES:**
- Módulo Lean `AbsSat.GraphPow` equivalente a `graph_pow.jl`.
- Módulos Lean `AbsSat.GraphPow.AbstractNode`, `.Filter`, `.Join`, `.Up` equivalentes a sus archivos Julia.
- Módulos Lean `AbsSat.Db.Machine.Cols.ColTimelineStep`, `.ColTimeline`, `.ColTimelinePowStep`, `.ColTimelinePow`.
- Módulos Lean `AbsSat.GraphPow.Reader` (`PathPowReader`, `PathPowExpReader`).
- Teoremas sobre invariantes de timelines (ej: consistencia de pasos, preservación de soluciones).
- Tests que validan la integración entre `GraphPow` y las colecciones de máquina.

**SUCCESS CRITERIA:**
1. `GraphPow` y sus operaciones están implementadas y su semántica coincide con Julia.
2. Las colecciones de máquina permiten registrar y consultar grafos por paso de tiempo.
3. Los lectores de `GraphPow` pueden recorrer caminos de potencia de manera consistente.
4. El código compila y los tests pasan.

**MICROTASKS:**
0002, 0003, 0004, 0005, 0006, 0007, 0040, 0041, 0042, 0043, 0044, 0045, 0046, 0047, 0048, 0049, 0050
**DEPENDENCIES:**
P3 (GraphMap), P5 (GraphPath avanzado)

**RISKS & MITIGATIONS:**
- **Riesgo**: `GraphPow` es una extensión compleja que depende de `GraphMap` y `GraphPath`.
  **Mitigación**: Asegurar que P3 y P5 estén completas antes de empezar P6; usar interfaces bien definidas.
- **Riesgo**: Las timelines requieren manejo de estado global (paso actual, contadores) que es difícil de modelar.
  **Mitigación**: Usar mónadas `StateT` o estructuras inmutables que capturen el estado completo.
- **Riesgo**: La visualización (`graph_pow_visual.jl`) es opcional.
  **Mitigación**: Posponerla o separarla como módulo no verificado.

---

**NOTES:**
- Referencia: `docs/original_julia/src/graph_pow/` y `docs/original_julia/src/db/machine/cols/`.
- `GraphPow` es clave para la escalabilidad del solver (trabajar con potencias del grafo).
- Las timelines son esenciales para el algoritmo principal (`SatMachine`).
