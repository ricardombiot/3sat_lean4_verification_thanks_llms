# Verificación para el Autor v114: Tseitin sobre Petersen — la máquina construye un Φ erróneo

Ricardo, soy Claude (Opus 5). Este informe trata **solo de la máquina**: una fórmula insatisfacible
para la que construye un conjunto Φ no vacío y responde SAT. El Reader va aparte, en v113. Aquí
explico cómo lo encontré, cómo lo verifiqué, dónde nace exactamente el error, por qué el review no lo
detecta y qué reglas podrían evitarlo.

---

## 1. El caso

`lean_project/Probes/cnf/ar/tseitin_petersen_H.cnf`: **fórmula de Tseitin sobre el grafo de
Petersen**. Hay una variable por arista (15) y, por cada vértice, las 4 cláusulas que imponen que la
paridad de sus 3 aristas sea su carga. La carga es 1 en el vértice 0 y 0 en el resto. Son 40 cláusulas,
todas con 3 variables distintas.

La suma de las aristas en todos los vértices cuenta cada arista dos veces, así que es par, y la suma de
cargas es impar. Por eso **la fórmula es insatisfacible**, y además mínimamente: quitar cualquier
cláusula la vuelve satisfacible.

**Verificado por cuatro vías independientes:**

| vía | resultado |
|---|---|
| fuerza bruta (2¹⁵ asignaciones) | **0 modelos** |
| `lake exe pure-sat-machine` | **`SATISFIABLE: 1 solutions found`** |
| modelo puro (`pureRun`, sonda) | línea final con 1 estado **válido, 330 nodos, 0 cadenas completas** |
| `lake exe improves-diff` (arnés diferencial) | base / débil / pines / SAC(1) = SAT; oráculo = UNSAT → **MISMATCH** |

El estado final es un **zombi**: sus tablas de owners son coherentes y pasan la validez, pero no
representan ninguna solución.

## 2. Cuándo falla y cuándo no

Tseitin sobre otros grafos cúbicos, con el mismo generador:

| grafo | vértices | cintura (ciclo más corto) | veredicto |
|---|---|---|---|
| K4 | 4 | 3 | UNSAT, correcto |
| K3,3 | 6 | 4 | UNSAT, correcto |
| prisma | 6 | 3 | UNSAT, correcto |
| cubo | 8 | 4 | UNSAT, correcto |
| prisma pentagonal | 10 | 4 | UNSAT, correcto |
| escalera de Möbius | 10 | 4 | UNSAT, correcto |
| **Petersen**, orden natural | 10 | 5 | **SAT, erróneo** |
| Petersen, aristas renumeradas (semilla 1) | 10 | 5 | UNSAT, correcto |
| Petersen, aristas renumeradas (semillas 2 y 3) | 10 | 5 | **SAT, erróneo** |
| Petersen, cláusulas barajadas (semillas 1 y 2) | 10 | 5 | UNSAT, correcto (8× más lento) |

Los grafos de 10 vértices con cintura 4 se deciden bien, así que no es cuestión de tamaño. Petersen
falla en 3 de los 6 órdenes probados, así que **el fallo depende también del orden** de variables y
cláusulas. Dos explicaciones simples no separan los casos: la cintura sola no (Petersen acierta con
algunos órdenes) y la adyacencia de los números de las aristas del corte tampoco (hay variables
consecutivas tanto en un orden que falla como en uno que acierta). No tengo todavía la caracterización
exacta del orden.

Los ficheros están en `lean_project/Probes/cnf/tseitin10/`.

## 3. Dónde nace el error, paso a paso

Modo nuevo de la sonda: `lake exe join-borrow trace <cnf>`. Avanza la máquina paso a paso, busca en
cada línea estados válidos sin ninguna cadena y, en el primer paso donde aparecen, examina cada envío
que los crea y qué subconjuntos de sus pines tienen solución.

En Petersen (orden natural):

- Pasos 1 a 66: **ningún estado zombi**. Las cláusulas de los vértices 0 a 8 se procesan bien.
- **Paso 67**, la primera cláusula del **vértice 9**, el último: aparecen **4 estados zombis**, uno
  por cada fila de esa cláusula con paridad **par** sobre las aristas del vértice 9 (`x10`, `x12`,
  `x13`).
- Para cada envío que los crea:
  - el estado de origen **sí tiene cadenas**;
  - tras filtrar con los pines de la fila, el estado es **válido pero sin cadenas**;
  - **cada pin solo y cada par de pines tiene cadenas**; los **tres juntos, ninguna**.

Ejemplo: el envío de `(66,7)` a `(67,1)` fija `x10=0, x12=0, x13=0`. `{x10=0}`, `{x12=0}`, `{x13=0}`,
`{x10=0, x12=0}`, `{x10=0, x13=0}` y `{x12=0, x13=0}` tienen solución; `{x10=0, x12=0, x13=0}` no.

En las dos renumeraciones que fallan el mecanismo es el mismo: paso 67, primera cláusula del último
vértice, tres pines de las aristas del corte, coherentes dos a dos y sin solución juntos.

## 4. Por qué el review no lo detecta

**La restricción que falta tiene tres variables.** Los vértices 0 a 8 suman carga impar. Sumando sus
restricciones de paridad, cada arista interna aparece dos veces y se cancela, y queda que las aristas
que salen hacia el vértice 9 tienen paridad impar:

    x10 ⊕ x12 ⊕ x13 = 1

Esa igualdad no está en ninguna cláusula. Se deduce **combinando los nueve vértices**. Y es una
restricción de tres variables: fijando dos de ellas, la tercera queda determinada, pero cualquier par
de valores es posible.

**La máquina razona por parejas.** Las tablas de owners dicen qué nodos pueden ir juntos de dos en
dos, y el review propaga esa información. Un par de pines nunca contradice la paridad, porque la
tercera arista siempre se puede ajustar. La contradicción solo aparece con los tres pines a la vez, y
esa información no está en ningún par. Es exactamente el hueco de Helly de los fantasmas, pero ahora
en el filtro de un envío, sobre los pines de una fila de cláusula.

**Por qué justo aquí.** Las tres aristas del vértice 9 solo comparten cláusula en las del propio
vértice 9. En Petersen sus tres vecinos (4, 6 y 7) están a distancia 3 entre sí sin pasar por él: no
hay ningún ciclo de 4 que acerque dos de esas aristas en otro vértice. En los grafos de cintura 4 hay
un camino más corto por el que la información de paridad de dos aristas del corte se fusiona antes.
Eso explica que la dificultad aparezca con cintura 5, pero no por qué unos órdenes aciertan y otros no.

**No son entradas obsoletas.** Cada pin y cada par de pines tiene cadenas reales, así que las tablas
no están mal por parejas. Están bien por parejas y no bastan.

## 5. Qué hipótesis caen con este caso

- **`SendExact`**: el envío `(66,7) → (67,1)` la viola literalmente. El origen es no vacío, el filtro
  es válido y ningún camino del origen pasa por los tres pines.
- **`FrontierSend`**: no hay ningún modelo de las cláusulas 0 a 35 cuya fila en la cláusula 36 sea la
  fijada, porque los vértices 0 a 8 obligan a paridad impar en el corte.
- **La solidez del veredicto** ("línea final no vacía ⇒ satisfacible"), y con ella `FinalReadable` y
  `AuthorReadable` sobre todos los estados finales.

**Lo que sigue en pie:**
- **completitud y conservación**: la máquina nunca pierde soluciones, y una respuesta **UNSAT es
  siempre correcta**;
- todos los teoremas condicionales demostrados: siguen siendo verdad, pero su hipótesis falla para
  esta fórmula.

## 6. Reglas candidatas para que no construya mal

Tras cada una indico si es correcta (no pierde soluciones) y hasta dónde llega.

1. **Certificado fuera de la máquina.** Responder SAT solo cuando el Reader exhibe una asignación y se
   comprueba contra las cláusulas; si no la encuentra, responder "no concluyente".
   - Correcta y sencilla, y no toca el review. **Elimina todos los SAT falsos**, porque las respuestas
     UNSAT ya son siempre correctas.
   - No hace que la máquina decida bien: en este caso respondería "no concluyente" en vez de UNSAT.
   - Es la única regla de esta lista que protege en todos los casos.

2. **Soporte triple para los pines de una fila de cláusula.** Al filtrar con los tres pines, exigir
   en cada paso un nodo compatible con los tres a la vez, no solo con cada par.
   - Es correcta y apunta exactamente al hueco de este caso.
   - Pero es de anchura fija. Tu memoria registra que la forma triple ya fue insuficiente en el
     contexto del cierre `R`, y con grafos de ciclos más largos la restricción que falta puede
     necesitar más variables que los tres pines. Merece un prototipo en la máquina *Improves*, sin
     esperar que sea general.

3. **Consistencia condicionada (SAC).** Fijar un nodo y propagar por parejas puede revelar una
   restricción de tres variables: con `x10` fijado, `x12` y `x13` quedan ligadas por parejas.
   - Correcta (ya existe como variante, con su prueba de conservación).
   - **Falla en este caso con una y con tres pasadas** (sección 7). Fijar un solo nodo no basta: la
     restricción que falta necesita razonar sobre los nueve vértices a la vez, no sobre un par
     condicionado.

4. **Razonamiento XOR (eliminación gaussiana).** Detectar grupos de cláusulas que codifican paridades
   y derivar sus combinaciones lineales como cláusulas nuevas.
   - Correcta, y resolvería Tseitin en cualquier grafo.
   - Pero solo esa familia: no ayuda con contradicciones que no sean lineales.

5. **Orden de cláusulas.** Con las cláusulas barajadas la máquina acierta aquí.
   - No cambia la corrección, solo el recorrido.
   - No da ninguna garantía (no sabemos qué orden evita el problema en general) y aquí fue 8 veces
     más lento.

6. **Comprobación global en cada envío.** Tras filtrar, buscar una cadena completa y descartar el
   estado si no la hay.
   - Exacta: eliminaría los zombis en su origen.
   - Pero es una búsqueda con backtracking cuyo coste puede crecer exponencialmente, lo contrario de lo
     que busca el diseño de la máquina.

**Recomendación:** adoptar ya la 1, que da seguridad inmediata sin cambiar la máquina, y prototipar la
2 en la máquina *Improves*, midiéndola sobre la familia de Tseitin con grafos de cintura creciente. La
3 queda descartada para este caso por la medición.

## 7. SAC con tres pasadas

`lake exe improves-diff --sac 3` sobre la misma fórmula: base / débil / pines / SAC(3) = SAT, oráculo =
UNSAT, **MISMATCH**. SAC(3) elimina exactamente lo mismo que SAC(1) (`sacCut` = 162.507 en ambos) y
tarda 82 s frente a 57 s. Las pasadas extra no encuentran nada nuevo, así que la consistencia
condicionada en un nodo no alcanza a ver esta restricción.

## 8. Siguiente

1. Caracterizar el orden: qué distingue los órdenes en que la máquina acierta con Petersen.
2. Prototipar el soporte triple en la máquina *Improves* y medir Tseitin sobre grafos de cintura 5 y 6
   (dodecaedro, Heawood).
3. Añadir el certificado al Reader ejecutable.
