**TASK ID:** 0001

**ROLE:** Project Director

**PRIORITY:** Alta

**DEPENDENCIES:** Ninguna

**SHOULD TARGET:**  
Analizar la documentación del proyecto (`project_main.md` y `/docs`) y desglosarla en fases secuenciales (P1, P2, …). Para cada fase, crear entre 20 y 100 microtareas de alta‑media granularidad (cada una completable en ≤30 minutos), asignando a cada microtarea el campo PHASE correspondiente y definiendo dependencias reales que pueden cruzar fases para evitar trabajo redundante. Crear los archivos de fase en `tasks/phases/`, los archivos individuales de microtareas en `tasks/work/` y configurar el archivo `tasks/next_task.md` inicial siguiendo la plantilla `tasks/templates/next_tasks.md`.

**SHOULD DO:**  
1. Leer y comprender `project_main.md` y toda la documentación adjunta en `/docs`.
2. Identificar las fases secuenciales del proyecto (P1, P2, P3…) basándose en hitos naturales o componentes principales.
3. Para cada fase identificada:
   a. Crear un archivo `tasks/phases/phase_PX.md` siguiendo la plantilla `tasks/templates/phase.md`.
   b. En el archivo de fase, completar OBJECTIVES, DELIVERABLES, SUCCESS CRITERIA, DEPENDENCIES (fases previas) y RISKS & MITIGATIONS.
4. Dividir cada fase en 20‑100 microtareas de alta‑media granularidad, asegurando que cada una:
   - Tenga una descripción clara y detallada.
   - Tenga criterios de aceptación verificables (objetivos o técnicamente obvios).
   - Tenga dependencias bien definidas con otras microtareas, pudiendo estas apuntar a tareas de fases anteriores o de la misma fase (dependencias cruz‑fase).
   - Sea completable en ≤30 minutos (granularidad adecuada).
   - Incluya el campo PHASE con el identificador de la fase correspondiente.
5. Generar un archivo `tasks/work/task_XXXX.md` para cada microtarea, siguiendo la plantilla `tasks/templates/task.md`. Los TASK IDs deben ser secuenciales a partir de 0002.
6. Actualizar el campo MICROTASKS en cada archivo de fase con los TASK IDs de las microtareas pertenecientes a esa fase.
7. Crear el archivo `tasks/next_task.md` inicial, incluyendo:
   - PROJECT ARCHITECTURE, PROJECT TARGET, CURRENT STATE y SPRINT TARGET basados en la documentación.
   - Una lista de ACTIVE TASKS (máximo 3) con las microtareas más prioritarias (independientemente de su fase).
   - Un BACKLOG priorizado con el resto de microtareas, ordenado por dependencias y valor.
   - La sección COMPLETED TASKS vacía.
   - LAST UPDATED con la fecha y hora actual.
8. Verificar que todas las microtareas tienen una estructura coherente, que las dependencias son lógicas (sin ciclos) y que el desglose cubre todo el proyecto.

**ACCEPTANCE CRITERIA:**  
1. Se han creado archivos de fase en `tasks/phases/` para cada fase identificada, siguiendo la plantilla `tasks/templates/phase.md`.
2. Se han creado entre 40 y 100 archivos `tasks/work/task_XXXX.md` (desde 0002 en adelante).
3. Cada archivo de microtarea sigue exactamente la plantilla `tasks/templates/task.md` con todos los campos completos, incluyendo el campo PHASE.
4. Las dependencias entre microtareas son lógicas, no contienen ciclos y pueden cruzar fases cuando sea necesario para evitar trabajo redundante.
5. El archivo `tasks/next_task.md` sigue exactamente el formato de `tasks/templates/next_tasks.md`.
6. Las 3 microtareas en ACTIVE TASKS son las más críticas para iniciar el proyecto (independientemente de su fase).
7. El BACKLOG está ordenado por prioridad y dependencias.
8. Todas las microtareas tienen granularidad adecuada para ser completadas en ≤30 minutos.

**RESOURCES:**  
- `project_main.md`
- `/docs/` (toda la documentación anexa)

**POTENTIAL RISKS:**  
- La documentación puede ser insuficiente o ambigua, requiriendo interpretación.
- El desglose puede ser demasiado fino o demasiado grueso, afectando la eficiencia del ciclo autónomo.
- Pueden surgir dependencias no anticipadas que requieran ajustes posteriores.

**SCOPE:**  
Esta tarea solo incluye el desglose del proyecto en microtareas y la creación de los archivos correspondientes. No incluye la implementación de ninguna funcionalidad del proyecto. Quedan excluidas modificaciones a la documentación original y la ejecución de las microtareas generadas.
