# Plantilla de Fase de Proyecto

**PHASE ID:** P5

**PHASE NAME:** GraphPath avanzado y lectores

**OBJECTIVES:**
- Migrar las funciones avanzadas de `GraphPath` (filtrado, join, up, constructores) y los lectores de paths.
- Verificar propiedades de los algoritmos de manipulación de caminos.
- Implementar la interfaz de lectura (`PathReader`, `PathExpReader`) para recorrer caminos.

**DELIVERABLES:**
- Módulo Lean `AbsSat.GraphPath.Constructor` equivalente a `graph_path_constructor.jl`.
- Módulo Lean `AbsSat.GraphPath.Filter` equivalente a `graph_path_filter.jl`.
- Módulo Lean `AbsSat.GraphPath.Join` equivalente a `graph_path_join.jl`.
- Módulo Lean `AbsSat.GraphPath.Up` equivalente a `graph_path_up.jl`.
- Módulo Lean `AbsSat.GraphPath.Reader` equivalente a `path_reader.jl` y `path_exp_reader.jl`.
- Teoremas sobre correctitud de los algoritmos (ej: `is_valid_node`, `is_valid_join`).
- Tests que validan el comportamiento de los lectores.

**SUCCESS CRITERIA:**
1. Todas las funciones avanzadas de `GraphPath` están implementadas en Lean y su semántica coincide con Julia.
2. Los lectores pueden recorrer caminos y extraer información de manera consistente.
3. Los invariantes de filtrado y join están formalizados (ej: un join válido preserva la estructura de árbol).
4. El código compila y los tests pasan.

**MICROTASKS:**
0032, 0033, 0034, 0035, 0036, 0037, 0038, 0039
**DEPENDENCIES:**
P4 (Colecciones de paths y GraphPath base)

**RISKS & MITIGATIONS:**
- **Riesgo**: Los algoritmos de join y up pueden ser complejos y depender de invariantes no triviales.
  **Mitigación**: Dividir cada algoritmo en pasos verificables independientes y probar con casos pequeños.
- **Riesgo**: Los lectores (`PathReader`) implican estado mutable (posición actual) que es difícil de modelar en Lean.
  **Mitigación**: Usar estructuras persistentes que devuelvan un nuevo lector tras cada operación (estilo `StateT`).
- **Riesgo**: La función `graph_path_visual.jl` es opcional para la verificación.
  **Mitigación**: Posponerla o separarla como módulo no verificado (igual que en P3).

---

**NOTES:**
- Referencia: `docs/original_julia/src/graph_path/` (archivos avanzados y `reader/`).
- Estas funciones son cruciales para la generación y manipulación de caminos durante la resolución SAT.
- Considerar usar mónadas `StateT` para modelar el estado de los lectores.
