# Certificación por Equivalencia en Lean 4

## 1. El Concepto del "Oráculo"

Cuando diseñamos un algoritmo altamente optimizado (como la máquina de grafos `GPathM`), su código fuente suele estar lleno de operaciones complejas: punteros, recolección de basura, uniones de conjuntos, filtros, etc. Si le decimos a un matemático o informático "confía en mí, este código de 5.000 líneas resuelve el problema 3SAT correctamente", es muy probable que desconfíe. Podría haber un pequeño *bug* en la lógica de filtrado o en la construcción del grafo.

Para solucionar esto de forma indiscutible, usamos un **Oráculo**. Un oráculo es un algoritmo alternativo que cumple estas dos propiedades:
1. **Es ineficiente:** No nos importa su rendimiento, porque solo se usa para las demostraciones matemáticas, nunca se ejecuta en producción.
2. **Es estúpidamente simple:** Su lógica es tan sencilla y pura que cualquier persona (incluso alguien sin experiencia en programación avanzada) puede leerlo y decir: "Sí, es matemáticamente imposible que esto se equivoque".

En nuestro caso, el oráculo es el **algoritmo de fuerza bruta** (`BruteForce.lean`). Genera el árbol de $2^N$ posibles combinaciones de booleanos y evalúa la fórmula en todas y cada una de ellas.

---

## 2. Los Certificados del Oráculo

Para que la comunidad científica y Lean 4 confíen en el Oráculo, hemos demostrado dos teoremas sobre él (ver `BruteForce.lean`):

*   **Soundness (Corrección - `bruteForceSat_sound`):** Si el Oráculo dice que una asignación es válida, significa que matemáticamente satisface la fórmula lógica.
*   **Completeness (Completitud - `bruteForceSat_complete`):** Si existe en el universo platónico una asignación que satisface la fórmula, el Oráculo la va a encontrar y a añadir a su lista.

Con estos dos teoremas, hemos demostrado que `bruteForceSat` **es la definición computable perfecta de la verdad absoluta** para una fórmula dada.

---

## 3. Definiendo las Soluciones de la Máquina

El siguiente paso en tu repositorio es abstraer el concepto de "solución" que tiene tu máquina de grafos. Tu máquina no devuelve una lista de booleanos directamente; mantiene un grafo (`GPathM`) con "caminos vivos".

Utilizando tus definiciones, sabemos que un camino vivo se comprueba con `denotS g p`, y que existe una función `decode` para extraer los booleanos. 

Debemos definir matemáticamente el conjunto de soluciones que tu máquina afirma haber encontrado al finalizar su ejecución:

```lean
-- Las asignaciones extraídas de todos los caminos que sobrevivieron en el grafo
def machineSolutions (g : GPathM) : Set Assign :=
  { a : Assign | ∃ (sel : Int → PathNodeId), 
      denotS g (pathOf sel g) ∧ decode sel = a }
```

---

## 4. El Teorema Final (El Puente de Equivalencia)

El objetivo central ("El Jefe Final") de tu trabajo de verificación formal es demostrar que, una vez la máquina de grafos ha terminado de ingerir y procesar la fórmula completa (`is_final_state φ g`), los conjuntos de soluciones coinciden **exactamente**.

```lean
theorem GPathM_is_correct (φ : Cnf) (hwf : WF φ) (g : GPathM) (h_final : is_final_state φ g) :
    machineSolutions g = { a | ∃ l ∈ bruteForceSat φ, toAssign l = a }
```

Si logras probar este teorema en Lean 4, habrás conseguido el **santo grial de la informática teórica aplicada**: habrás demostrado que tu máquina optimizada en C/C++ calcula exactamente lo mismo que el concepto matemático abstracto de 3SAT, sin fisuras ni bugs.

---

## 5. La Vía para Demostrarlo (Estrategia de Prueba)

Demostrar que dos conjuntos son iguales en Lean requiere demostrar dos cosas: $A \subseteq B$ y $B \subseteq A$. 

Tu máquina se construye paso a paso (semántica de bucle/pasos). Por lo tanto, esta demostración no se hace "de golpe" al final, sino que requiere un **Invariante Inductivo** que se mantenga cierto en cada paso (añadir un nodo, hacer un join, aplicar un filtro).

### Paso A: Soundness de la Máquina ($A \subseteq B$)
**"Todo lo que sobrevive en mi grafo es correcto."**
Debes demostrar que las operaciones como `upSons`, `join`, etc., nunca se inventan un camino falso.
*   **¿Qué tienes ya hecho?** ¡Casi todo! El teorema `denotS_sound` en `SubsetSemantics.lean` ya dice: *"Si un camino está en mi denotación, la asignación decodificada satisface la fórmula procesada hasta el paso K" (`SatUpTo φ ...`).*
*   **Lo que falta:** Simplemente unificar eso para decir "si ha llegado al paso N, entonces satisface la fórmula entera (`Sat`)", lo cual conecta instantáneamente con el Oráculo.

### Paso B: Completeness de la Máquina ($B \subseteq A$)
**"Si una solución es correcta en el Oráculo, mi máquina no la ha borrado por accidente."**
Esta es, por convención, la parte más difícil de verificar en los SAT Solvers.
Debes realizar inducción sobre las operaciones de tu máquina.
*   Si empiezo con la semilla inicial (`initSeed`), tengo todas las soluciones posibles.
*   Si aplico un filtro (`upFiltering`), debo probar matemáticamente que: *Si un camino viejo era lógicamente válido para la nueva cláusula, la función del filtro evalúa a `true` y el camino no es destruido en el nuevo grafo.*
*   Si hago uniones o limpiezas de nodos muertos, debo probar que no me llevo por delante ningún camino que decodifique en una asignación correcta.

### Resumen del Flujo de Trabajo a Seguir:
1. Asegúrate de que las definiciones semánticas de `Assign` encajan bien en ambos lados.
2. Demuestra el Invariante A (Soundness) para cada operación de la máquina.
3. Demuestra el Invariante B (Completeness) para cada operación de la máquina.
4. Juntas todo en el `GPathM_is_correct`.
