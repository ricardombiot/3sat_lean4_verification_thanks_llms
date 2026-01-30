# Plantilla de Fase de Proyecto

**PHASE ID:** P3

**PHASE NAME:** GraphMap y importación CNF

**OBJECTIVES:**
- Migrar el módulo `GraphMap` de Julia a Lean 4, incluyendo la construcción del grafo de asignaciones.
- Implementar la importación de fórmulas CNF para inicializar el grafo.
- Verificar propiedades estructurales del grafo (conexión, etapas, invariantes).

**DELIVERABLES:**
- Módulo Lean `AbsSat.GraphMap` equivalente a `graph_map.jl`.
- Módulo Lean `AbsSat.GraphMap.ImportCnf` equivalente a `graph_map_import_cnf.jl`.
- Teoremas sobre correctitud de `add_var!`, `add_gate!`, `close_vars!`, etc.
- Tests que validan la construcción del grafo para instancias CNF pequeñas.

**SUCCESS CRITERIA:**
1. La estructura `GMap` se puede crear y modificar mediante las operaciones equivalentes a las de Julia.
2. La importación de un archivo CNF genera un `GMap` con el número correcto de variables, cláusulas y nodos.
3. Los invariantes del grafo (ej: cada nodo tiene padres válidos, los pasos son secuenciales) están formalizados.
4. El código compila y los tests pasan.

**MICROTASKS:**
0026, 0027, 0028, 0029, 0030, 0031
**DEPENDENCIES:**
P2 (Colecciones de mapas)

**RISKS & MITIGATIONS:**
- **Riesgo**: La lógica de `add_gate!` y `add_gate_case!` es compleja y depende de múltiples pasos.
  **Mitigación**: Dividir en microtareas pequeñas, cada una verificando un sub‑comportamiento.
- **Riesgo**: La importación CNF maneja formatos de archivo y parsing, que puede ser tedioso en Lean.
  **Mitigación**: Usar un parser simple (línea a línea) y limitarse al subconjunto 3SAT necesario.
- **Riesgo**: La visualización (`graph_map_visual.jl`) podría ser opcional para la verificación.
  **Mitigación**: Posponer la visualización a una fase posterior o separarla como módulo no verificado.

---

**NOTES:**
- Referencia: `docs/original_julia/src/graph_map/`
- `GraphMap` es el corazón del algoritmo; su correcta migración es crítica.
- Considerar usar `Lean.IO` para la lectura de archivos CNF, o simularla con datos hard‑coded en pruebas.
