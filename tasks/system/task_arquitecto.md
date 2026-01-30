**TASK ID:** 0000

**ROLE:** Architect

**PRIORITY:** Crítica (se activa automáticamente)

**DEPENDENCIES:** Ninguna (puede ejecutarse en cualquier momento)

**SHOULD TARGET:**  
Diagnosticar y corregir problemas estructurales en el desglose de microtareas que están causando fallos recurrentes o bloqueos en el proyecto. Revisar y redefinir microtareas problemáticas, crear nuevas microtareas para cubrir brechas técnicas o de diseño, y reorganizar el backlog y las tareas activas para asegurar la viabilidad del proyecto.

**SHOULD DO:**  
1. Analizar el estado actual del proyecto, incluyendo:
   - Microtareas que han fallado 2 o más veces consecutivas (marcadas con "[FALLO RECURRENTE]").
   - Bloqueos identificados en los PRs recientes.
   - Dependencias cíclicas o mal definidas.
   - Brechas en la cobertura técnica o de diseño.
2. Revisar la documentación del proyecto (`project_main.md` y `/docs`) para entender el contexto y los objetivos.
3. Revisar y corregir la definición de las microtareas problemáticas:
   - Ajustar dependencias para eliminar ciclos y mejorar el flujo.
   - Clarificar o redefinir criterios de aceptación.
   - Ajustar el alcance (SCOPE) para que sea realista en ≤30 minutos (granularidad adecuada).
   - Actualizar los campos PRIORITY y POTENTIAL RISKS según sea necesario.
4. Crear nuevas microtareas (en `tasks/work/`) para cubrir brechas identificadas, siguiendo la plantilla `tasks/templates/task.md`.
5. Reorganizar el backlog y las tareas activas en `tasks/next_task.md`:
   - Asegurar que las tareas activas (máximo 3) sean ejecutables y prioritarias.
   - Reordenar el backlog por prioridad y dependencias.
   - Mover tareas fallidas recurrentemente a una posición adecuada o marcarlas para revisión adicional.
6. Actualizar el campo "CURRENT STATE" en `tasks/next_task.md` con un resumen de los cambios estructurales realizados.
7. Una vez completada la intervención, marcar esta tarea (task_arquitecto.md) como completada y **removerla de `tasks/next_task.md`** (no debe permanecer activa continuamente).

**ACCEPTANCE CRITERIA:**  
1. Las microtareas problemáticas (fallos recurrentes) han sido redefinidas con dependencias y criterios de aceptación claros.
2. No quedan dependencias cíclicas en el conjunto de microtareas.
3. Se han creado las microtareas adicionales necesarias para cubrir brechas técnicas o de diseño.
4. El backlog y las tareas activas reflejan un plan viable y están ordenados por prioridad y dependencias.
5. `tasks/next_task.md` sigue exactamente el formato de `tasks/templates/next_tasks.md`.
6. Esta tarea (task_arquitecto.md) ha sido marcada como completada y eliminada de la lista de tareas activas en `tasks/next_task.md`.

**RESOURCES:**  
- `project_main.md`
- `/docs/` (toda la documentación anexa)
- Historial de PRs y commits del proyecto.
- Archivos de microtareas existentes en `tasks/work/`.

**POTENTIAL RISKS:**  
- La intervención del arquitecto podría introducir cambios demasiado grandes, rompiendo la granularidad de ≤30 minutos.
- Puede ser difícil diagnosticar la causa raíz de los fallos recurrentes sin acceso a logs detallados.
- El tiempo asignado puede ser insuficiente para un análisis profundo en proyectos complejos.

**SCOPE:**  
Esta tarea solo incluye intervención en la definición de microtareas y en la estructura del backlog. No incluye la implementación directa de funcionalidades del proyecto. Quedan excluidas modificaciones a la documentación original (`project_main.md` y `/docs`) a menos que sean correcciones menores de claridad. El arquitecto no debe ejecutar microtareas de desarrollo, solo redefinirlas y reorganizarlas.
