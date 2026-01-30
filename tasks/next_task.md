PROJECT ARCHITECTURE:
Migración del algoritmo SAT de Julia a Lean 4. El código original en Julia (docs/original_julia/src/) está organizado en módulos: db/, graph_map/, graph_path/, graph_pow/, sat_machine/, utils/. La migración sigue una estructura similar en Lean (docs/lean/abs_sat/) con verificación formal de cada función.

PROJECT TARGET:
Migrar el algoritmo SAT de Julia a Lean 4, verificando formalmente cada parte (2‑3 funciones por microtarea) con teoremas en Lean, respetando el diseño original pero adaptándose para favorecer la verificación formal.

CURRENT STATE:
Completed task 0022. The `PathDocOwners` structure and its basic API (`new`, `isValid`, `have`, `get`, `insert`, `remove`) have been migrated and verified.

SPRINT TARGET:
Completar las microtareas de las fases P1 (tipos fundamentales y colecciones de mapas) para establecer la base del proyecto y validar el ciclo de desarrollo.

---

## ACTIVE TASKS (Máximo 3)

- [ ] tasks/work/task_0023.md — Migrate and verify `have`, `get` from `path_doc_owners.jl`.

---

## BACKLOG (Priorizado)

### Fase P1 (Utils)

### Fase P2 (DB)

### Fase P3 (GraphMap)

### Fase P4 (GraphPath)

### Fase P5 (GraphPow)

### Fase P6 (SatMachine)

---

## COMPLETED TASKS (Últimas 5)

- [x] tasks/work/task_0022.md — Migrate and verify `new`, `is_valid` from `path_doc_owners.jl`. (Completado: 2025-12-29)
- [x] tasks/work/task_0021.md — Migrate and verify `get_step` and `add_son!` from `path_doc_node.jl`. (Completado: 2025-12-29)
- [x] tasks/work/task_0020.md — Migrate and verify `new` and `is_root` from `path_doc_node.jl`. (Completado: 2025-12-28)
- [x] tasks/work/task_0019.md — Migrate and verify `get_node` and `is_empty` from `path_col_nodes.jl`. (Completado: 2025-12-28)
- [x] tasks/work/task_0018.md — Migrate and verify `new` and `for_each` from `path_col_nodes.jl`. (Completado: 2025-12-28)

---

**LAST UPDATED:** 2025-12-29T15:00:00Z
**NEXT UPDATE TRIGGER:** Tras merge de PR de microtarea completada

---

**REMEBER AFTER ALWAYS MUST DO:**
- MUST WRITE los ficheros de microtareas individuales en `tasks/work/task_XXXX.md` siguiendo la plantilla `tasks/templates/task.md` de microtarea Jules.
- MUST ACTUALIZAR `tasks/next_task.md` con las microtareas prioritarias para el sprint, siguiendo la plantilla de `tasks/templates/next_tasks.md`.
- MUST COMMIT RESULTS siguiendo el formato: "**TASK ID:** XXXX | RESULT: [Descripción breve del resultado y enlace a los ficheros creados]".
