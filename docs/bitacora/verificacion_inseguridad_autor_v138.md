# Verificación para el Autor v138: el veredicto desde una ecuación global — la unión de reviews

Ricardo, soy Claude (Opus 5). Me dijiste que tu estructura, para ser leída, tiene que estar **completa, no
parcial**, y que quizá ahí residía la dificultad. Tenías razón en un sentido preciso: todas las reglas
locales que refuté (v130–v132) miraban tablas sueltas, y tu lector nunca lee tablas sueltas; fija una
elección y **vuelve a revisar la estructura entera**. Así que busqué una propiedad de **operaciones
enteras**, no de tablas, y la encontré, la medí y la formalicé.

Resultado en tres frases:

1. **El veredicto SAT está demostrado en Lean a partir de una sola hipótesis sobre el review**
   (`ReviewJoin`): revisar una unión da algo contenido en la unión de lo revisado.
2. **Esa hipótesis se cumple en cada medida**: 0 diferencias en ~90.000 comprobaciones tabla a tabla.
3. **El núcleo que queda para demostrarla es un enunciado combinatorio preciso** sobre conjuntos de
   apoyo, con la teoría de punto fijo que necesita ya demostrada en el proyecto.

Rama `spaik`, build de `AbsSat` (195 jobs), sin `sorry`, `[propext, Quot.sound]`.

---

## 1. La ecuación: el envío distribuye sobre la unión

Tu máquina tiene tres operaciones: envío (filtro débil, fijaciones, review, UP), unión por clave y
lectura. La pregunta global es:

> ¿Enviar la unión de dos estados es lo mismo que unir sus envíos?

La sonda `helly distrib` lo compara **tabla a tabla** en cada unión de la ejecución, para el envío a cada
hijo y para el review del lector:

| familias | comprobaciones | diferencias |
|---|---|---|
| Tseitin K4, K3,3, prisma, cubo, Petersen (par) + paridad k3 | ~3.600 | **0** |
| aleatorias, semillas 1001 / 2002 / 3003 | 87.611 | **0** |

Incluidas las 16.480 veces en que solo sobrevive un lado: entonces el envío de la unión es exactamente
el del lado vivo. **El envío distribuye sobre la unión, exactamente.**

## 2. Lo que se deduce de ella (demostrado)

`SendDistrib.lean`:

* **`split_branch`** — una rama válida se parte, en **cualquier** paso, en trozos de una sola clave, y
  uno de ellos es válido **por sí solo**. Es la inducción sobre la construcción: la ejecución desde una
  línea queda dentro de la mezcla de las ejecuciones desde cada una de sus entradas. La mezcla es la
  misma operación que hace tu driver (`insertPure`); no entra nada nuevo.
* **`noBorrow_of_distrib`** — eso es exactamente `NoBorrow` (v127): *en cada estado del lector alguna
  elección tiene su rama válida por sí misma, no prestada por una unión*.
* **`sat_of_distrib`** — y de `NoBorrow` el veredicto (ya demostrado en v127): estado final válido ⟹ φ
  satisfacible.

`ReviewJoin.lean` reduce las dos ecuaciones a **una**, sobre el review solo:

* **el filtro débil y las fijaciones conmutan con la unión literalmente** (`filterWeakAll_join`,
  `foldl_filterRequire_join`): solo filtran los owners globales, y los de la unión son una unión;
* **el UP distribuye** (`embedded_addNode_join`): los dos lados añaden el mismo nodo nuevo, con la misma
  clave;
* por tanto **`ReviewJoin`** basta: *fijar y revisar la unión de dos estados de una línea da un estado
  contenido en la unión de los lados revisados que siguen válidos*. De ella salen `SendDistrib`,
  `ReviewDistrib` y el veredicto (`sat_of_reviewJoin`).

Lo importante: **no hay ningún lema de pares, tríos ni cadenas**. Toda la dificultad está en una
igualdad entre dos operaciones sobre la estructura entera, que es como tú dices que hay que leerla.

## 3. El núcleo: por qué el review de una unión no toma prestado

`ReviewJoin` es la afirmación de que el review —un máximo punto fijo— no gana apoyo mezclando los dos
lados. Medí las dos formas naturales de demostrarlo:

| enunciado | significado | medida |
|---|---|---|
| **restricción** | lo que el review de la unión deja en las tablas del lado a es ya un punto fijo | **falla**: 72 en paridad, 841 / 989 en aleatorias (~4 %) |
| **cobertura** | revisar cada una de las dos restricciones y unirlas recupera todo el review de la unión | **0 fallos** en 27.290 comprobaciones |

La primera falla por un motivo concreto: hay entradas que están en **las dos** tablas pero que solo se
sostienen con apoyo del otro lado. Al restringir a un lado pierden su apoyo; al restringir al otro lo
conservan. Así que el reparto correcto no es "por pertenencia", sino "por dónde se sostiene", y eso es
exactamente la cobertura.

Y la herramienta para demostrarla **ya existe**: `AnchoredSurvive.Sup` es la noción de *conjunto de
apoyo* dentro de un estado, y `AOk_filterAllAgg` demuestra que **todo conjunto de apoyo sobrevive a las
fijaciones compatibles y al review**. Es la propiedad de máximo punto fijo. Con ella el núcleo queda
como un enunciado combinatorio:

> **Partición de apoyos.** El apoyo que el review de la unión sostiene se parte en un apoyo dentro de a
> y un apoyo dentro de b.

Si se demuestra, cada parte sobrevive al review de su lado y `ReviewJoin` sale inmediatamente.

## 4. Cómo queda todo

| afirmación | estado |
|---|---|
| UNSAT: ejecución vacía ⟹ φ insatisfacible | demostrado sin hipótesis |
| SAT con camino | demostrado sin hipótesis |
| el conjunto de la máquina = los certificados (v136) | demostrado sin hipótesis |
| **estado final válido ⟹ φ satisfacible** | **demostrado bajo `ReviewJoin`** — una hipótesis sobre el review solo, medida sin excepción |
| `ReviewJoin` | abierta; reducida (con la teoría de punto fijo existente) a la **partición de apoyos** |

Las hipótesis anteriores (`CommonOwner`, `ValidDecidesEmpty`) siguen siendo suficientes, pero
`ReviewJoin` es de otra naturaleza: no habla de lo que la estructura contiene, sino de que **dos
operaciones de tu máquina conmutan**. Es una propiedad del diseño, se comprueba en cada unión, y su
demostración no pasa por ningún paso de pares a conjuntos que no sea el propio review.

## 5. Qué atacaría ahora

La partición de apoyos, usando lo que ya sabemos de la estructura de una unión:

* los nodos del paso alto son **exclusivos** de cada lado (claves (destino, origen) distintas);
* **la rebanada de un nodo exclusivo vive en su lado** (`slice_of_exclusive_top`, v129);
* todo apoyo tiene, por la condición `agg` de `Sup`, un testigo **en el paso alto**.

La idea: repartir cada entrada según el lado de su testigo en el paso alto. Es la versión en punto fijo
del criterio del paso alto que medí exacto en v129 ("una elección sobrevive en el lado i si y solo si
tiene un nodo alto exclusivo de i"). Lo que falta ver es si ese reparto cumple las condiciones de
apoyo, en particular la de padres; esa es la parte que v129 dejó abierta en su forma estática y que
ahora se puede atacar con el punto fijo delante.

## 6. Artefactos

* Lean: `AbsSat/GraphPath/Model/SendDistrib.lean`, `AbsSat/GraphPath/Model/ReviewJoin.lean`,
  `join_parents_source` en `Join.lean`.
* Sondas (`lean_project/Probes/Helly.lean`): `distrib`, `restrict` (restricción y cobertura); también
  `futures` y `nested` de v137.
