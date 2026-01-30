# Plantilla de Fase de Proyecto

**PHASE ID:** P4

**PHASE NAME:** Colecciones de paths y GraphPath base

**OBJECTIVES:**
- Migrar las estructuras de datos de colecciones para `GraphPath` desde Julia a Lean 4.
- Implementar las operaciones básicas de construcción y manipulación de caminos.
- Verificar propiedades de consistencia de las colecciones de paths.

**DELIVERABLES:**
- Módulo Lean `AbsSat.Db.Path.Cols.PathColNodes` equivalente a `db/path/cols/path_col_nodes.jl`.
- Módulo Lean `AbsSat.Db.Path.Cols.PathColLines` equivalente a `db/path/cols/path_col_lines.jl`.
- Módulo Lean `AbsSat.GraphPath` básico (parte de `graph_path.jl`).
- Teoremas sobre invariantes (ej: unicidad de IDs en paths, relaciones padre‑hijo).
- Tests unitarios para las operaciones CRUD.

**SUCCESS CRITERIA:**
1. Las colecciones `PathColNodes` y `PathColLines` están implementadas y sus operaciones (`push_node!`, `link_nodes!`, `get_node`, etc.) son equivalentes a Julia.
2. La estructura `GPath` básica se puede crear y manipular.
3. Los invariantes de las colecciones están formalizados (ej: un nodo de path tiene un padre existente).
4. El código compila y los tests pasan.

**MICROTASKS:**
0015, 0016, 0017, 0018, 0019
**DEPENDENCIES:**
P1 (Tipos fundamentales)

**RISKS & MITIGATIONS:**
- **Riesgo**: Las colecciones de paths tienen relaciones más complejas (árbol de caminos) que las de mapas.
  **Mitigación**: Modelar las relaciones con tipos inductivos que capturen la estructura de árbol.
- **Riesgo**: La función `graph_path.jl` es extensa y puede tener dependencias de otras partes no migradas.
  **Mitigación**: Migrar primero las funciones básicas de construcción y dejar las avanzadas para P5.
- **Riesgo**: Las operaciones de filtrado y join (en `graph_path_filter.jl`, `graph_path_join.jl`) son complejas.
  **Mitigación**: Posponerlas a P5, centrándose en P4 solo en la estructura de datos y operaciones simples.

---

**NOTES:**
- Referencia: `docs/original_julia/src/db/path/cols/` y `docs/original_julia/src/graph_path/graph_path.jl` (parte inicial).
- Las colecciones de paths son análogas a las de mapas, pero con semántica de caminos.
- Considerar usar `Std.AssocList` o `Lean.Data.HashMap` para las colecciones, igual que en P2.
