# Verificación para el Autor v140: el invariante de rebanadas por construcción, y el invariante de vuelta

Ricardo, soy Claude (Opus 5). Este informe recoge lo hecho tras v139: formalicé tu invariante de
**rebanadas** a lo largo de toda la construcción, medí **cómo** tu review elimina las compatibilidades
falsas tras una fijación, y reduje todo lo abierto a un enunciado sobre **una sola pasada** del review
base. También cuento con claridad lo que intenté para demostrar ese último paso y por qué no salió.

Rama `spaik`, build de `AbsSat` (200 jobs), sin `sorry`, `[propext, Quot.sound]`. Commits `192760a`,
`e800bdd`, `bf0e6fd`.

---

## 1. Tu ciclo, en tus palabras y en Lean

Tu descripción del envío:

> antes del UP fijamos los requisitos borrando todos los nodos que no los cumplen (así rompemos todos
> esos caminos parcialmente construidos); luego el review deja el grafo estable; y si es válido creamos un
> nuevo nodo que toma los owners globales como sus owners, compatible con todos, y lo añadimos a todas
> las tablas.

Y del review:

> lo que buscamos es incoherencia, configuraciones que no son caminos; si eliminamos todas las
> incoherencias dejando solo las compatibles tenemos la rebanada exacta.

El **invariante de rebanadas** —la tabla de cada nodo es exactamente el conjunto de nodos de los caminos
que pasan por él— es la exactitud de v135 (`TablesSound` + `TablesComplete`). Lo formalicé **por
construcción** en `SliceInvariant.lean`:

| paso de tu ciclo | conserva las rebanadas |
|---|---|
| semilla | demostrado (`tablesSound_initSeed`) |
| **UP**: el nuevo nodo toma el estado entero como tabla | demostrado (`tablesSound_addNode`): tu diseño lo hace gratis |
| unión por clave | demostrado (`tablesSound_join`) |
| **fijar + review** | hipótesis `FilterSlices` |

* **`run_slices`** — con esa hipótesis, **todos** los estados de la ejecución tienen rebanadas por tablas.
* **`sat_of_slices`** — y el veredicto sale directo: un estado válido tiene un owner global, que se posee a
  sí mismo, así que su rebanada contiene un camino entero, que es un modelo.

## 2. Cómo mata tu review las compatibilidades falsas (medido)

Llamo **fantasma** a una entrada de tabla que, tras una fijación, ya no sostiene ningún camino
superviviente. La sonda `helly ghosts` reproduce el review paso a paso —limpieza con la tabla global,
coherencia con padres, con hijos, bucle base, barrido agresivo, y otra vuelta si quitó algo— y registra
qué operación mata cada fantasma. Todas las fijaciones posibles, sobre todos los estados exactos de K4 y
de paridad:

| | K4 | paridad |
|---|---|---|
| fantasmas | 1.243.728 | 1.780.588 |
| **sobreviven al review** | **0** | **0** |
| mueren en la 1.ª pasada del review base: limpieza | 1.043.549 (916.072 con el nodo entero) | 1.357.408 |
| mueren en la 1.ª pasada: padres | 153.408 | 298.661 |
| mueren en la 1.ª pasada: hijos | 43.451 | 123.075 |
| mueren en la 2.ª pasada | **0** | **0** |
| mueren en el **primer barrido agresivo** | 3.320 | 1.444 |
| mueren en una segunda vuelta exterior | **0** | **0** |

Y las que llegan al barrido son **siempre detectables por pares**, exactamente por las dos patas de tu
filtro agresivo:

| fantasmas que llegan al barrido | K4 | paridad |
|---|---|---|
| **asimétricas** (v ya no posee a x) | 2.728 | 1.276 |
| **algún paso sin owner común** | 592 | 168 |
| no detectables directamente | **0** | **0** |

Tu comentario de que el barrido agresivo hacía falta para Tseitin se ve aquí: mata pocas, pero son
justamente las que padres e hijos no ven.

## 3. El invariante de vuelta (demostrado que basta)

`RoundInvariant.lean`:

* **`GhostsDetectable B R`** — tras el review base `B` del estado fijado, toda entrada es asimétrica, o
  sus dos tablas no comparten nada en algún paso, o está en un camino del resultado final `R`.
* **`tablesSound_of_ghosts`** — **entonces todas las tablas finales son rebanadas.** La prueba no necesita
  razonar sobre el orden del barrido: el resultado final es simétrico y comparte owner en cada paso
  (`aggOk_reviewAgg`), y sus tablas están dentro de las del review base (`pruned_review_reviewAgg`), así
  que una entrada detectable en `B` no puede llegar a `R`.
* **`filterSlices_of_ghosts`**, **`sat_of_ghosts`** — el invariante de rebanadas de toda la ejecución, y el
  veredicto, bajo **`GhostsLine`**: el invariante de vuelta en cada estado fijado de la ejecución.

## 4. El intento de demostrar `GhostsLine`, y por qué no salió

`GhostsLine` habla solo del **review base** (el más estudiado del proyecto) aplicado a un estado que era
**exacto** antes de fijar. Intenté la inducción sobre los pasos que la estructura de la pasada sugiere, y
medí antes cada posible base:

| posible base de inducción | resultado |
|---|---|
| tras la pasada de padres (de arriba abajo), la parte inferior de cada tabla por encima de la fijación ya es exacta; y lo simétrico con hijos | **falso**: las cuatro direcciones conservan fantasmas hasta el barrido (K4, tras padres: 720 / 1.032 / 43.675 / 1.344) |
| el nodo que suelta primero una fantasma es el más cercano a la fijación | **falso**: repartido (K4: 1.352 frente a 1.296) |

Junto con lo refutado en v139 —uniones arbitrarias, cadenas enlazadas, Helly-3, rebanada cerrada por
enlaces, dominancia del ancla— son **nueve** formas locales, estáticas o direccionales, todas falsas. Solo
es cierta la afirmación global: tras una pasada, las fantasmas quedan en una forma que tu barrido
reconoce.

## 5. Dos vías que quedan, y su valoración

* **Deconstrucción**: el estado es exactamente la unión de los caminos del oráculo (v139). Si eso se
  demuestra con igualdad, el filtro se reduce a una pregunta sin nada de la máquina: el review de la
  unión de **todas** las soluciones de requisitos "y ⇒ r", tras fijar, ¿es exacto? Medido exacto en
  22.486 casos (v139, `pathcsp`); falso para uniones arbitrarias.
* **Reducción a un lema combinatorio independiente**: el mismo enunciado, sin máquina. Permite una
  **búsqueda adversarial** de contraejemplos, rápida y exhaustiva, en lugar de probar familias al azar.
* La **reducción por contraejemplo mínimo** (al estilo del teorema de los cuatro colores) no la veo
  viable: exigiría que detectar una fantasma dependiera de una ventana acotada de pasos, y las
  restricciones alcanzan pasos lejanos.

## 6. Cómo queda todo

| afirmación | estado |
|---|---|
| UNSAT: ejecución vacía ⟹ φ insatisfacible | demostrado sin hipótesis |
| la máquina es el oráculo, en la dirección que protege UNSAT | demostrado sin hipótesis |
| un camino del oráculo que sobrevive solo ⟹ SAT | demostrado sin hipótesis |
| toda entrada revisada está en una cadena enlazada | demostrado sin hipótesis |
| semilla, UP y unión conservan las rebanadas | demostrado sin hipótesis |
| fijar + review conserva las rebanadas ⟸ `GhostsLine` | demostrado |
| **`GhostsLine`**: tras una pasada del review base sobre un estado exacto fijado, toda compatibilidad falsa es asimétrica o le falta un owner común | **medido sin excepción; abierto** |
| estado final válido ⟹ φ satisfacible | demostrado bajo `GhostsLine` |

El siguiente informe (v141) fija `GhostsLine` como la hipótesis declarada del resultado.
