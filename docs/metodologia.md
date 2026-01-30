# Metodología de Migración y Verificación Formal con Microtareas

## 1. Introducción

### Propósito
Este documento describe la metodología sistemática utilizada en el proyecto **Jules** para migrar el algoritmo `AbsSat` desde Julia a Lean 4, creando microtareas de verificación formal. El objetivo es proporcionar una guía replicable para proyectos similares que requieran migrar algoritmos imperativos a un lenguaje de verificación formal, manteniendo el diseño original pero adaptándose para facilitar la verificación.

### Alcance
La metodología cubre:
- La descomposición del código fuente original en microtareas manejables.
- La creación automatizada de microtareas utilizando scripts Python.
- La verificación formal en Lean 4, incluyendo tips para preservar la semántica original mientras se favorece la verificación.
- Consideraciones de gestión de proyectos (fases, dependencias, roles).

### Audiencia
- **Desarrolladores** que implementarán la migración.
- **Verificadores** que redactarán y demostrarán teoremas.
- **Gestores de proyecto** que planificarán y supervisarán el progreso.
- **Arquitectos** que diseñarán la estructura del proyecto Lean.

## 2. Metodología General de Migración y Verificación

### Fases del proyecto
El proyecto se divide en fases (`P1` a `P7`) basadas en dependencias lógicas y componentes del algoritmo:
- **P1**: Utilidades y estructuras de datos básicas.
- **P2**: Componentes de mapeo (`map`).
- **P3**: Grafo de mapeo (`graph_map`).
- **P4**: Componentes de caminos (`path`).
- **P5**: Grafo de caminos (`graph_path`).
- **P6**: Grafo de potencia (`graph_pow`).
- **P7**: Máquina SAT y verificadores finales.

Cada fase agrupa archivos relacionados; las microtareas dentro de una fase pueden ejecutarse en paralelo una vez satisfechas las dependencias de fases anteriores.

### Enfoque incremental
- **Lotes pequeños**: Migrar de 2 a 3 funciones por microtarea. Esto mantiene cada tarea abordable y permite verificación temprana.
- **Verificación continua**: Cada microtarea incluye la demostración de teoremas que garantizan propiedades clave. No se avanza a la siguiente microtarea hasta que los criterios de aceptación se cumplan.
- **Integración progresiva**: A medida que se completan microtareas, se integran en el proyecto Lean y se comprueba la coherencia global.

### Principios clave
1. **Respetar la semántica original**: La implementación en Lean debe producir los mismos resultados que el código Julia para los mismos inputs.
2. **Diseñar una abstracción funcional pura**: Para facilitar la verificación, se crea un modelo funcional puro que captura la lógica del algoritmo sin efectos secundarios (ej. `PureSatMachine`).
3. **Especificación antes de implementación**: Definir predicados formales (ej. `Solvable`, `is_valid_solution`) que describan las propiedades deseadas, luego implementar y demostrar que se satisfacen.
4. **Correspondencia con el original**: Usar evaluaciones (`#eval`) para comparar resultados con el código Julia y asegurar la corrección de la migración.

## 3. Creación Automatizada de Microtareas

### Paso 1: Inventario de funciones
Se utiliza el script `scripts/inventory_julia_functions.py` para analizar el código fuente original (Julia) y generar un archivo CSV (`julia_functions_inventory.csv`) que lista todas las funciones, su ubicación (archivo, línea) y otras metadatos.

### Paso 2: Agrupación por archivo y fase
El script `scripts/generate_microtasks.py` define un mapeo (`PHASE_MAP`) que asigna cada archivo Julia a una fase. Este mapeo se basa en las dependencias lógicas identificadas en el diseño del proyecto.

### Paso 3: División en chunks
Las funciones de cada archivo se dividen en lotes de 2 a 3 (configurable) para mantener microtareas manejables. Cada lote se convierte en una microtarea independiente.

### Paso 4: Generación de archivos de microtarea
Cada microtarea se escribe en `tasks/work/task_XXXX.md` utilizando la plantilla `tasks/templates/task.md`. La plantilla incluye:
- **TASK ID**: Identificador único de 4 dígitos.
- **ROLE**: Rol responsable (ej. Developer, QA).
- **PHASE**: Fase a la que pertenece.
- **PRIORITY**: Prioridad (Alta/Media/Baja) basada en dependencias y valor.
- **DEPENDENCIES**: Lista de TASK IDs que deben completarse antes.
- **SHOULD TARGET**: Objetivo claro y medible.
- **SHOULD DO**: Pasos detallados para realizar la tarea.
- **ACCEPTANCE CRITERIA**: Criterios verificables, incluyendo demostración de teoremas.
- **RESOURCES**: Enlaces a código original, documentación, etc.
- **POTENTIAL RISKS**: Riesgos anticipados y alternativas.
- **SCOPE**: Alcance explícito de la microtarea.

### Paso 5: Actualización de fases
El script actualiza los archivos `tasks/phases/phase_PX.md` incluyendo la lista de IDs de microtareas asignadas a cada fase.

### Paso 6: Resumen
Se genera un archivo `tasks/microtasks_summary.md` con el conteo total y distribución por fase.

**Ventajas de la automatización**:
- Consistencia en la documentación.
- Actualización fácil al cambiar el mapeo de fases.
- Escalabilidad para proyectos grandes.

## 4. Verificación Formal con Lean 4: Tips para Mantener el Diseño Original

### 4.1 Abstracción funcional pura
- **Motivación**: Los algoritmos imperativos suelen usar mutabilidad y E/S, que son difíciles de verificar. Se crea un modelo funcional puro que capture la lógica central.
- **Ejemplo**: En `AbsSat`, se definió `PureSatMachine` con tipos inductivos para `PureGMap` y `PurePath`, y una función `evolve_path` que representa la transición de estados sin efectos secundarios.
- **Beneficio**: Este modelo es más fácil de razonar matemáticamente y permite demostrar teoremas de corrección.

### 4.2 Especificación de propiedades
- **Predicados de corrección**: Definir predicados que capturen las propiedades deseadas del algoritmo. Por ejemplo:
  - `Solvable (gmap : PureGMap) : Prop` indica que existe una solución válida para el grafo.
  - `is_valid_solution (gmap : PureGMap) (path : PurePath) : Prop` especifica cuándo un camino es una solución válida.
- **Independencia del algoritmo**: Estos predicados se definen en términos del problema, no de la implementación, lo que permite comparar diferentes algoritmos.

### 4.3 Teoremas fundamentales
Para garantizar la corrección, se demuestran dos teoremas principales:
1. **Soundness (Solidez)**: Todo output del algoritmo es una solución válida.
   ```lean
   theorem soundness (gmap : PureGMap) (path : PurePath) :
       path ∈ run_pure gmap → is_valid_solution gmap path := by
     ...
   ```
2. **Completeness (Completitud)**: Si existe una solución, el algoritmo la encontrará.
   ```lean
   theorem completeness (gmap : PureGMap) :
       Solvable gmap → ∃ path, path ∈ run_pure gmap := by
     ...
   ```
Juntos, estos teoremas aseguran que el algoritmo es correcto para **cualquier** instancia del problema.

### 4.4 Tips prácticos para la migración
- **Representar estructuras mutables como tipos inductivos**: En lugar de arrays mutables, usar `List` o `Array` inmutable en Lean. Si es necesario, modelar la mutabilidad con un estado que se pasa como parámetro.
- **Conservar la interfaz de funciones**: Mantener los nombres y parámetros de las funciones originales cuando sea posible, pero cambiar la implementación interna para ser más verificable.
- **Usar `#eval` para validar correspondencia**: Después de implementar una función en Lean, ejecutarla con ejemplos concretos y comparar los resultados con los de Julia. Esto ayuda a detectar errores de traducción.
- **Escribir lemas auxiliares**: Descomponer teoremas complejos en lemas más pequeños sobre propiedades locales. Esto facilita las demostraciones y reutiliza razonamiento.
- **Leverage el sistema de tipos de Lean**: Usar tipos dependientes para codificar invariantes (ej. `{n : Nat // n > 0}`) y reducir la necesidad de precondiciones explícitas.
- **Pruebas por inducción estructural**: Dado que los datos del SAT son finitos, se puede usar inducción sobre el tamaño del grafo o la longitud del camino.

### 4.5 Estrategia de verificación
1. **Modelar el algoritmo puro**.
2. **Definir especificaciones formales** (predicados).
3. **Implementar las funciones** en Lean, siguiendo el modelo puro.
4. **Demostrar teoremas de corrección** (soundness, completeness) usando el modelo.
5. **Conectar la implementación con el modelo** mediante teoremas de equivalencia.
6. **Validar con ejemplos** para asegurar que la implementación coincide con el comportamiento original.

## 5. Consideraciones Adicionales para Replicar en Otros Proyectos

### 5.1 Gestión de dependencias
- **Grafo de dependencias**: Definir claramente las dependencias entre fases y microtareas. Las herramientas de automatización pueden generar este grafo a partir del mapeo de fases.
- **Priorización**: Ejecutar primero las microtareas de fases con menos dependencias (ej. P1, P2) para desbloquear trabajo posterior.

### 5.2 Asignación de roles
- **Developer**: Responsable de la implementación en Lean y de escribir los teoremas.
- **QA**: Revisa las demostraciones, ejecuta ejemplos y verifica los criterios de aceptación.
- **Project Manager**: Prioriza microtareas, asigna recursos y supervisa el progreso.
- **Architect**: Diseña la estructura del proyecto Lean y el mapeo de fases.

### 5.3 Control de riesgos
- **Riesgos identificados**:
  1. **Dependencias no migradas**: Una función puede requerir otras funciones que aún no se han migrado. Mitigación: migrar en orden según el grafo de dependencias.
  2. **Semántica no directamente traducible**: Algunos constructos de Julia (ej. mutabilidad, manejo de errores) no tienen equivalente directo en Lean. Mitigación: diseñar una abstracción que capture la esencia sin copiar los detalles de implementación.
  3. **Demostraciones no triviales**: La verificación formal puede requerir lemas matemáticos complejos. Mitigación: dividir la demostración en pasos más pequeños y consultar recursos de matemáticas relevantes.
- **Alternativas**: Si una función es demasiado compleja para verificar completamente, se puede:
  - Dejar como `axiom` temporalmente y documentar su supuesto.
  - Simplificar la especificación (aceptar una propiedad más débil pero verificable).
  - Refactorizar el código original para hacerlo más verificable.

### 5.4 Recursos necesarios
Cada microtarea debe incluir enlaces a:
- El código fuente original (archivo Julia).
- La documentación del proyecto (`project_main.md`, `config.md`).
- Ejemplos de verificación previa (teoremas ya demostrados en el proyecto).
- Recursos externos (tutoriales de Lean, bibliotecas matemáticas).

### 5.5 Automatización y adaptación
- **Scripts reutilizables**: Los scripts `inventory_julia_functions.py` y `generate_microtasks.py` pueden adaptarse a otros proyectos modificando:
  - La expresión regular para detectar funciones (en Julia, Python, etc.).
  - El mapeo de fases (`PHASE_MAP`) según la estructura del nuevo proyecto.
  - El tamaño del chunk (número de funciones por microtarea).
- **Plantillas personalizables**: La plantilla `task.md` puede extenderse con campos específicos del dominio (ej. "Performance requirements", "Security considerations").

## 6. Conclusión y Recomendaciones

### Resumen de pasos
1. **Inventariar** las funciones del código original.
2. **Agrupar** por archivo y fase según dependencias.
3. **Generar microtareas** automatizadas con objetivos y criterios claros.
4. **Implementar** en Lean, respetando la semántica original.
5. **Verificar** con teoremas de soundness y completeness.
6. **Integrar** y validar con ejemplos.

### Métricas de éxito
- **Cantidad de funciones migradas** vs. total.
- **Número de teoremas demostrados** por función (idealmente ≥2).
- **Cobertura de especificaciones**: porcentaje de propiedades especificadas que han sido verificadas.
- **Tiempo de compilación**: el proyecto Lean debe compilar sin errores.

### Adaptabilidad
Esta metodología es aplicable a cualquier proyecto que:
- Tenga un código base en un lenguaje imperativo (Julia, Python, C++, etc.).
- Requiera verificación formal de propiedades críticas.
- Pueda ser modelado como un sistema de estados finitos.

Los ajustes principales serán en el mapeo de fases y en el diseño del modelo funcional puro, que debe capturar la esencia del algoritmo original.

---

*Documento generado como parte del proyecto de verificación de 3sat usando Jules IA. Última actualización: enero 2026.*
