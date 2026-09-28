# Verificación para el Autor v206: las etiquetas en Lean, dónde se paran, y una regla por pares de filas

Ricardo, este informe es corto. Cuenta lo que se hizo desde el v205, en la rama `row-tags`: llevar las etiquetas a
Lean, lo que eso demostró, el problema que apareció al diseñar el veredicto, la medida que lo confirma y la
propuesta siguiente, con su límite.

**La conclusión, por adelantado.**
* **Demostrado en Lean:** la máquina con etiquetas no pierde soluciones (`machineVerdictT_of_sat`, sin `sorry`, solo
  los axiomas estándar).
* **El veredicto sin hipótesis no sale con las etiquetas por fila.** La regla cierra cada fila por separado. La
  demostración necesita, al bajar por la línea, que las piezas de filas distintas se cierren **juntas**, y eso la regla
  no lo garantiza. Está medido: en el 40 % de los casos, la intersección de dos piezas no es cerrada.
* **El dato bueno:** aun así, ninguna cima se queda sin una estructura anidada para ningún par de filas.
* **La propuesta:** una regla que cierre las intersecciones de dos filas. Es polinómica y no pierde soluciones. **Su
  límite:** la demostración pide cadenas de todas las filas, y con pares no se cubren. Es un experimento, no un cierre.

---

## 1. Lo hecho en Lean (plan `docs/plans/lean_row_tags.md`)

**T1, la máquina con etiquetas** (`AbsSatBingo/Tagged/Defs.lean`). Es una capa aparte sobre `GPathB`, que no se toca:
`TGPath` es el estado más su lista de etiquetas `(par, fila, clave)`.
* Las operaciones son espejo de Julia: `stamp` en la llegada, `inheritTags` en el UP, `doJoinT` en el join,
  `tagSweep`/`tagCut` como la regla y su corte, y `reviewT` para el review.
* Encima, la máquina y el lector: `runT` y `readerVerdictT`.
* Un detalle que obligó a cambiar el diseño: las listas repetían etiquetas en cada join, porque las llegadas comparten
  la historia del remitente, y la máquina no terminaba ni en `basic_v3_c1`. Con una unión sin repetidas
  (`tagUnion`), `basic_v3_c1` termina en 32 s y coincide con la fuerza bruta (ejecutable `tagged-check`).

**T2, no se pierde ninguna solución** (`Tagged/Carried.lean`, `Tagged/Keeps.lean`, `Tagged/Machine.lean`):
* `TagCarried`: la camarilla de una solución lleva, en cada fila, la clave por la que pasa.
* `cliqueTags_tagSweep` y `carried_tagCut`: la regla no le quita ninguna etiqueta, y el corte no le quita ningún nodo
  ni arista. Es el argumento de solidez del v204 §7.3, ya formal.
* Se conserva en la llegada, el UP (`hasTag_inherit`: la etiqueta de cada par nuevo sale de la del padre), el join,
  el filtro y el review.
* **`run_carriesT` y `machineVerdictT_of_sat`.**

Commits: `986b694` (T1 + T2) y `9a6b028` (el plan con el problema de la §2).

## 2. El problema, al diseñar el veredicto

La demostración del lector baja por la línea. En cada nivel:
1. en el join de arriba, la pieza de la cima (fila `n`, clave `a`) cae dentro de su llegada. **Esto la regla sí lo
   da**, y el v205 lo midió sin fallos;
2. dentro de esa llegada, la estructura tiene que volver a partirse en la fila `n−1`, **dentro de la pieza `a`** y
   con los pins del lector;
3. y así fila a fila hacia abajo.

La regla por filas solo asegura que cada pieza `(n−1, b)` del estado entero es cerrada. No asegura que lo sea su
intersección con la pieza `(n, a)`. Y en el nivel siguiente, la intersección acumula una fila más. La §7.4 del v204
(«la bajada respeta las etiquetas») era demasiado optimista, y la sonda de la unión solo había medido la fila del
join.

## 3. La medida (`test_3sat/probe_row_tags_nested.jl`, commit `c086e45`)

En los estados que visita el lector (fijados y revisados, con etiquetas), para cada par de filas mezcladas y cada
combinación de claves `(a, b)`, se toma la intersección de las dos piezas. Se comprueba con las mismas condiciones que
la regla y se calcula su mayor parte cerrada. Resultados en las 20 primeras instancias del corpus (sigue corriendo):

| | resultado |
|---|---|
| intersecciones miradas | 19 928 |
| **no cerradas tal cual** | **8 033 (40 %)** |
| nodos que pierden hasta su punto fijo | 138 300 |
| cimas que salen del punto fijo de alguna intersección | 2 805 |
| **cimas sin ninguna intersección cerrada para algún par de filas** | **0** |

Dos lecturas, y las dos cuentan:
* **La regla por filas no basta:** las intersecciones no se cierran solas.
* **Aun así, nada se pierde:** para cada par de filas, toda cima está en alguna intersección cuyo punto fijo la
  conserva. Una regla que cerrara las intersecciones no mataría ninguna cima, en lo medido.

## 4. La propuesta: una regla por pares de filas

**Propuesto.**

**Los datos.** Además de la máscara por fila, cada arista y cada nodo guardan, por cada par de filas mezcladas
`(ℓ₂, ℓ₁)`, qué combinaciones de claves `(a, b)` los sostienen. En bin son 4 bits por par de filas.
* En la llegada, la fila nueva se combina con lo que ya había en cada fila de abajo.
* En el UP, se hereda de los padres.
* En el join, OR par a par.

**La regla.** Es la regla de la etiqueta, aplicada a la pieza de cada intersección `(ℓ₂, a) ∩ (ℓ₁, b)`. Las funciones
de Julia `tag_node_keeps` y `tag_edge_keeps` ya reciben la pieza como argumento y sirven tal cual. Tras cada pasada:
* la máscara de fila se reduce a lo que sobrevive en los pares;
* muere lo que se queda sin combinaciones en algún par.

**Solidez (deducida):** una solución pasa por una combinación concreta en cada par de filas, y su camarilla está
entera en esa intersección, así que la regla no la toca. Es el mismo argumento que para las filas.

**Coste:** unos `S²/2 × 4` bits por arista (unos 2,5 KB con 100 filas) y un factor `S` más de tiempo sobre la regla
actual, que ya es ×25. Es polinómico, pero pesado.

**El límite, dicho claro:** la regla cierra intersecciones de **dos** filas. La bajada de la demostración añade una
fila por nivel (`(n, a) ∩ (n−1, b) ∩ (n−2, c) ∩ …`). Con pares no se cubren los tríos, y pedirlo para todas las filas
a la vez es pedir cadenas completas de claves, que son combinaciones exponenciales. Así que esta regla sirve para
**medir si con pares basta en la práctica**, no para cerrar la demostración tal como está planteada.

## 5. Estado de las corridas

* **Julia con etiquetas en el corpus** (en curso, 32 de 89): mismos veredictos que el exhaustivo, el lector sin pins
  muertos y con las hojas iguales a las soluciones, 0 aristas cortadas, memoria máxima 723 MB. Todas con el tope de
  memoria de `run_capped.sh`.
* **Intersecciones en el corpus** (en curso): los datos de la §3.
* **`tagged-check` de Lean** en 9 instancias pequeñas (en curso; el modelo en listas es lento).

## 6. Lo que sigue

1. Terminar la medida de intersecciones en el corpus entero. Si alguna cima se queda sin intersección cerrada para
   algún par de filas, esta vía se cierra.
2. Si se mantiene en 0, decidir si merece la pena implementar la regla por pares, sabiendo su límite (§4).
3. Lo demostrado (T1–T2) queda como resultado firme.

---

**Ficheros nuevos:** `lean/improves_bingo/AbsSatBingo/Tagged/{Defs,Carried,Keeps,Machine}.lean`,
`lean/improves_bingo/TaggedCheckMain.lean`, `julia/improves_bingo/test_3sat/probe_row_tags_nested.jl`.
