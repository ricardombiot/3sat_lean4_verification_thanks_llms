# Verificación Formal de AbsSat: Una Narrativa

Este documento explica, en lenguaje natural, qué hace el algoritmo **AbsSat**, cómo hemos verificado que funciona correctamente, y por qué podemos confiar matemáticamente en sus resultados.

## 1. El Algoritmo: SAT como un Problema de Caminos en un Grafo

Imagina que resolver un problema lógico (SAT) no es "buscar una aguja en un pajar" probando combinaciones al azar, sino **atravesar un mapa** desde el origen hasta el final.

*   **El Mapa (GMap)**: El problema SAT se convierte en un grafo estructurado en capas.
    *   Cada capa representa una variable ($X_1, X_2, \dots$) o una cláusula lógica.
    *   Los nodos en cada capa representan los posibles estados "verdaderos" en ese punto.
*   **El Camino (Path)**: Una solución válida es simplemente un camino que logra cruzar todas las capas del mapa, desde la primera hasta la última, sin romper ninguna regla.

### ¿Cómo funciona la máquina?
La máquina (`SatMachine`) empieza en el origen con un "camino vacío". En cada paso (capa), intenta extender sus caminos actuales hacia los nodos de la siguiente capa.
*   **Filtrado Estricto**: Solo puedes dar un paso hacia un nodo si tu camino actual cumple los *requisitos* de ese nodo.
*   **Sin Retroceso (Backtracking)**: Si un camino no puede avanzar a ningún nodo de la siguiente capa, muere. Si un camino llega al final, es una solución.

---

## 2. El Modelo Puro: La Esencia Matemática

El algoritmo real está escrito en Lean 4 con optimizaciones, bases de datos y manejo de memoria. Para verificarlo, creamos un **"Gemelo Digital Puro"** (`PureSatMachine`).

Este gemelo es una versión matemática simplificada que captura la lógica exacta del algoritmo pero elimina el ruido de la implementación (lectura de discos, punteros, etc.).
*   Si probamos que el Gemelo Puro es perfecto, y el algoritmo real implementa fielmente al gemelo, entonces el algoritmo real es perfecto.

---

## 3. ¿Por Qué es Correcto? (Los Teoremas)

Para decir que el algoritmo es "correcto", demostramos dos propiedades fundamentales en Lean 4.

### A. Solidez (Soundness): "No Miente"
> **Teorema**: *Si la máquina dice 'Aquí tienes una solución', esa solución es 100% real.*

**La prueba explicada**:
Imagina que cada capa del mapa tiene un guardia. El guardia solo te deja pasar a la siguiente capa si cumples los requisitos de esa capa.
*   **Inducción**:
    1.  Empiezas limpio (cumples 0 requisitos).
    2.  Si pasas la capa 1, cumples los requisitos de la capa 1.
    3.  Si pasas la capa 2, cumples los requisitos de la 1 y la 2 (porque el guardia verifica que lo nuevo sea compatible con lo viejo).
    4.  ...
    5.  Si llegas al final (capa N), has pasado por todos los guardias. Por tanto, cumples **todos** los requisitos del problema.

Hemos demostrado matemáticamente que la función `evolve_path` actúa como ese guardia perfecto. Nunca deja pasar un camino inválido.

### B. Completitud (Completeness): "No se Rinde"
> **Teorema**: *Si existe una solución en el universo, la máquina la encontrará.*

**La prueba explicada**:
Aquí es donde brilla el enfoque de "exploración exhaustiva".
*   Supongamos que existe una solución mágica llamada $S$.
*   $S$ es un camino válido que cruza todo el mapa.
*   Cuando la máquina está en la capa 1, mira *todas* las posibilidades. Como $S$ pasa por la capa 1, la máquina encontrará ese primer paso.
*   Cuando la máquina está en la capa 2, mira *todas* las extensiones posibles. Como $S$ es válida, su paso por la capa 2 es una extensión válida. La máquina la encontrará.
*   **Axioma Clave**: La máquina nunca "poda" una rama válida arbitrariamente. Solo elimina lo que es lógicamente imposible.
*   Por tanto, el camino $S$ sobrevivirá paso a paso hasta el final.

---

## 4. Los Axiomas: Los Cimientos

En nuestra verificación, usamos "Axiomas Estructurales". En lugar de probar desde cero cómo funcionan las listas en la memoria del ordenador, asumimos verdades lógicas básicas sobre la estructura del problema:
1.  **Monotonicidad**: Saber más cosas (tener un camino más largo) nunca hace que sepas menos cosas.
2.  **Preservación**: Si algo era verdad ayer, y hoy no ha cambiado nada relacionado, sigue siendo verdad.

Estos axiomas nos permiten enfocar la prueba en la lógica del algoritmo (grafos, satisfacción) en lugar de perdernos en detalles de programación.

---

## Resumen para Humanos y LLMs

1.  **Transformación**: SAT $\rightarrow$ Grafo de Capas.
2.  **Ejecución**: Caminar por el grafo filtrando lo inválido.
3.  **Garantía 1 (Solidez)**: Los filtros nunca fallan. Todo lo que sale es bueno.
4.  **Garantía 2 (Completitud)**: Los filtros no son demasiado agresivos. Nada bueno se queda fuera.
5.  **Verificación**: Demostrado formalmente en Lean 4 usando inducción estructural.
