# Plantilla de Fase de Proyecto

**PHASE ID:** P2

**PHASE NAME:** Colecciones de mapas

**OBJECTIVES:**
- Migrar las estructuras de datos de colecciones para `GraphMap` desde Julia a Lean 4.
- Implementar operaciones CRUD sobre colecciones de variables, nodos y líneas.
- Verificar propiedades de consistencia y correctitud de las operaciones.

**DELIVERABLES:**
- Módulo Lean `AbsSat.Db.Map.Cols.MapColVars` equivalente a `db/map/cols/map_col_vars.jl`.
- Módulo Lean `AbsSat.Db.Map.Cols.MapColNodes` equivalente a `db/map/cols/map_col_nodes.jl`.
- Módulo Lean `AbsSat.Db.Map.Cols.MapColLines` equivalente a `db/map/cols/map_col_lines.jl`.
- Teoremas que aseguren invariantes (ej: unicidad de IDs, preservación de relaciones padre‑hijo).
- Tests unitarios que validan las operaciones básicas.

**SUCCESS CRITERIA:**
1. Las tres colecciones tienen implementaciones Lean que reflejan la semántica de las originales.
2. Las funciones `register_var!`, `get_step_var`, `push_node!`, `link_nodes!`, `get_node`, etc. están implementadas y verificadas.
3. Los invariantes clave (ej: `get_node` retorna `Nothing` si el ID no existe) están formalizados como lemas.
4. El código compila y los tests pasan.

**MICROTASKS:**
0008, 0009, 0010, 0011, 0012, 0013
**DEPENDENCIES:**
P1 (Tipos fundamentales)

**RISKS & MITIGATIONS:**
- **Riesgo**: Las operaciones mutables (`register_var!`, `push_node!`) son difíciles de modelar en Lean (estado persistente).
  **Mitigación**: Usar mónadas `StateT` o estructuras persistentes (árboles) que devuelvan un nuevo estado.
- **Riesgo**: Las dependencias entre colecciones (ej: `link_nodes!` requiere que ambos nodos existan) pueden generar condiciones de error no capturadas.
  **Mitigación**: Usar tipos dependientes (`Option` o `Except`) para manejar errores y probar casos de borde.
- **Riesgo**: La eficiencia de las estructuras persistentes puede ser inferior a la de Julia (arrays mutables).
  **Mitigación**: Aceptar diferencia de rendimiento en esta etapa; optimizar después de tener la verificación correcta.

---

**NOTES:**
- Referencia: `docs/original_julia/src/db/map/cols/`
- Las colecciones son la base de `GraphMap`; es crucial que sus operaciones sean correctas.
- Considerar usar `Std.AssocList` o `Lean.Data.HashMap` para implementar los mapas.
