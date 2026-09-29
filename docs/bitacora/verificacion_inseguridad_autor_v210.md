# Verificación para el Autor v210: la bajada del lector, el join partido en piezas y la historia de las llegadas

Ricardo, este informe sigue al v209 en la misma sesión (29-sept-2026, rama `reader-stuck`). El v209 terminaba con el
veredicto del lector bajo una sola hipótesis sobre la unión (`UnionTopClique`). Aquí cuento tres cosas:
* cómo formalicé la bajada del lector (fijar y revisar), siguiendo tu observación sobre la compresión;
* cómo partí la hipótesis del join en piezas más pequeñas;
* cómo la parte "de lado" se redujo a hechos sobre la **historia de las llegadas** de dos remitentes.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * la bajada del lector dentro de toda estructura cerrada (`ChainInv`), por toda la línea;
  * `StarJoinDown` ⟺ `UnionTopClique` en el join;
  * la partición del join en B1 (Helly en la unión) y B2 (pureza de lado);
  * B2 ⇐ StarOneSide;
  * StarOneSide ⇐ `CrossAt` + `GapDead`;
  * la conexión con los remitentes de la línea (`tree_single`: en el mapa bin el destino es una sola llegada);
  * D2 (una cima de una llegada no vive en la otra);
  * `GapDead` ⇐ `ArrivalGap`.
* **El veredicto** (`readerVerdict_iff_of_senders3`) depende ahora de **tres hipótesis**:
  * **B1**: `StarNodes` de la unión;
  * **CrossAt**: sobre dos remitentes de la misma línea;
  * **ArrivalGap**: sobre la llegada de un remitente y la de otro.

  Las dos últimas ya no hablan de estructuras cerradas: son hechos sobre los grafos de dos remitentes y sus llegadas.
* **Medido:** las tres, con 0 fallos. B1 en el corpus completo; CrossAt y ArrivalGap en sondas rápidas de 3–10
  instancias, clause_mix incluida.

---

## 1. La bajada del lector: fijar y revisar (`ChainPin.lean`, `e3f0cb0`, `0b47e31`)

**Lo que falla.** Construir la selección válida que pasa por $z$ y $t$ bajando por padres y mirando solo las parejas
**se atasca** en los núcleos (`probe_greedy_descent.jl`): callejones en todas las instancias probadas, también dentro
de la vuelta de trío.

Tu observación lo explica: *la estructura contiene, comprimidas, todas las soluciones*. Una pareja puede venir de una
solución y la siguiente de otra.

**Lo que no falla.** Fijar y revisar tras cada elección, como hace el lector. Con eso **cualquier candidato sirve**: 0
candidatos malos y 0 atascos en 23 230 parejas.

En Lean:
* **`pinned_rel`**: en una estructura fijada desde un paso, todo nodo está relacionado con los fijados. Es la
  descompresión que evita el Helly.
* **`ChainInv`**: en una estructura fijada desde la cima, cualquier nodo se puede fijar también.
  * **`chainInv_up`**: demostrado sin hipótesis (bajar, fijar el padre con `StarInv`, subir con
    `secStruct_addNode_star`).
  * **`chainInv_join`**: desde `StarJoinDown`.
* **`carried_of_pinned`**: una estructura fijada en todos los pasos es una camarilla.
* **`topClique_of_chain`**: `ChainInv` + `StarInv` ⟹ `UnionTopClique`.
* **`starJoinDown_iff_unionClique`**: en el join las dos formas son equivalentes. La bajada del lector no quita la
  hipótesis del join, pero bajo ella **en todo estado fijar un nodo más dentro de una estructura fijada nunca la
  vacía**.

## 2. La dirección difícil, partida (`StarSplit.lean`, `7bde06b`)

`StarJoinDown` se construye con el punto fijo $F$ de la estrella de la cima $t$ en la unión. La partición es:

| pieza | qué dice | estado |
|---|---|---|
| **B1** | $F$ conserva $z$ (`StarNodes` de la unión) | hipótesis; 26 258 estrellas, 0 fallos |
| **B2** | una estructura dentro de la estrella solo usa aristas del lado de $t$ | ⇐ StarOneSide |
| **B3** | una estructura de la unión con aristas de un lado es cerrada en ese lado | **demostrado** (`secStruct_to_side`) |

**StarOneSide** es una afirmación sobre **el grafo de la unión**, sin estructuras: en la estrella de una cima, toda
pareja que no es del lado de la cima tiene un paso sin testigo común en la estrella. Medido: 150 051 parejas, 0 fallos,
tríos muertos incluidos. **`starPure_of_oneSide`**: StarOneSide ⟹ B2.

*Una corrección*: en el camino presenté como invariante nuevo que "las estrellas son cerradas por la vuelta de trío"
(0 huecos en 28 M parejas). Es trivial: en el paso del propio $w$ el único testigo posible es $w$. Las medidas de este
informe excluyen los pasos de los extremos.

## 3. StarOneSide por la historia de la pareja (`OneSideHist.lean`, `ad2b119`, `5c17156`)

El paso libre no está en un paso fijo:
* en el 89 % de las parejas, alguno está por encima de los extremos;
* en el 40 %, justo en el paso del remitente.

La clave fue mirar **de dónde viene la pareja**. Sea $y$–$w$ de $g$ y no de $e$, en la estrella de $t$, con $t$ en
$e$, y sea $A$ el remitente de $e$ (`probe_oneside_history.jl`, 10 instancias):

| caso | peso | mecanismo | estado |
|---|---|---|---|
| **ausente** (no estaba en $A$) | ~99 % | siempre en la estrella del **grupo de padres** de $t$ (1–2 padres con el mismo id y padre), con paso libre ya en el paso anterior | **demostrado** ⇐ `CrossAt` (`starOneSide_absent`) |
| **quitada** (estaba en $A$; la llegada la quitó) | ~1 % | siempre la regla de parejas; el hueco sigue libre en la unión porque los testigos de la otra llegada están **muertos en el lado** (790/790) | ⇐ `GapDead` |

**`starOneSideAt_of_hist`**: StarOneSide en el lado de una llegada ⇐ `CrossAt` + `GapDead` + D2.

La prueba del caso ausente descansa en dos hechos:
* la llegada solo quita aristas entre nodos viejos;
* la estrella de $t$ está dentro de la del grupo de sus padres, porque $t$ hereda sus vecinos.

## 4. La conexión con la línea (`LineCtxT.lean`, `SenderLink.lean`, `5b4c47d`, `34a4a67`, `87ef798`)

* **`run_provT`**: la inducción de la línea entrega a cada join su procedencia:
  * el estado del destino es un árbol de llegadas;
  * la llegada nueva es `arr φ kv key` de un remitente de la línea;
  * el invariante vale en todas las entradas de la línea.
* **`tree_single`**: en el mapa bin, el destino es **una sola llegada**. Sus orígenes son claves distintas de $s$ del
  paso del remitente, por tanto `other s`; con claves únicas, todas sus hojas son la misma llegada.
* **D2, demostrado** (`d2_of_pair`): las cimas de la llegada de $kv$ nacen como `shiftPid q d` de cimas del remitente,
  que son de `kv.1`. Así que llevan `parent_id = some kv.1`, y dos remitentes no comparten cimas.
* **ArrivalGap** (`probe_arrival_gap.jl`: 6 441 parejas quitadas en 565 llegadas, 0 fallos):
  > si la llegada de un remitente quita una pareja que el remitente tenía, hay un paso en el que ningún vivo de la
  > llegada es testigo común de la pareja, **ni siquiera usando las aristas de todas las llegadas del paso**.

  **`gapDead_of_arrivalGap`**: ArrivalGap ⟹ GapDead.

**`readerVerdict_iff_of_senders3`**: el veredicto del lector es la satisfacibilidad bajo
* **B1** en los joins,
* **CrossAt** en la estrella del grupo de padres, para cada par de remitentes con un hijo común,
* **ArrivalGap** para cada par de remitentes con un hijo común.

## 5. Lo que queda, y qué se sabe de cada pieza

| hipótesis | qué dice | datos | qué se sabe |
|---|---|---|---|
| **B1** | restringir una estructura de la unión a la estrella de una cima no pierde nodos | 26 258 / 0 | es el Helly de la unión; en el UP lo demostramos por inducción, en el join no |
| **CrossAt** | para dos remitentes: una pareja del otro que no es del propio tiene paso libre en la estrella de un grupo de cimas | 5 847 / 0 | por grupos vale; con todas las cimas falla (tríos muertos) |
| **ArrivalGap** | una pareja quitada por una llegada deja un hueco que ninguna llegada del paso tapa | 6 441 / 0 | ya con las aristas del remitente hay hueco (G1, 6 441/6 441); las otras llegadas sí añaden aristas (G2 falso), pero nunca tapan todos los pasos |

**La inducción de CrossAt** (`probe_cross_step.jl`). Al pasar de un paso de la línea al siguiente, las parejas de
CrossAt se reparten así:
* **~87 % quitadas** por la llegada: salen de **ArrivalGap**, porque la estrella del grupo está dentro de la llegada de
  su remitente. Está razonado, no formalizado.
* **~5 % ausentes dentro de un solo grupo**: heredan el paso libre, así que la inducción sirve.
* **~8 % ausentes repartidas** entre dos grupos del remitente: aquí aparece la versión con todas las cimas, que falla
  con los tríos muertos. Es el único hueco de la inducción de CrossAt.

Con eso, el fenómeno que se repite en GapDead y en la mayor parte de CrossAt es uno solo: **una llegada quita una
pareja y deja un hueco que nada de fuera tapa**. ArrivalGap es la forma más limpia que tenemos de él.

## 6. Siguiente paso propuesto

1. **Formalizar CrossAt ⇐ CrossAt anterior + ArrivalGap** para los casos "quitado" y "ausente en un grupo", dejando el
   caso "repartido" como hipótesis explícita. Así se sabría exactamente cuánto de CrossAt es inductivo.
2. **Estudiar el caso "repartido"** (~8 %) con una sonda pequeña: si el filtro del destino mata siempre lo que falla
   en la versión con todas las cimas, CrossAt quedaría como invariante de la línea bajo ArrivalGap.
3. **ArrivalGap**: G1 dice que el hueco nace en el remitente (los testigos que el remitente tenía en ese paso mueren
   todos en la llegada). Falta ver por qué las aristas nuevas de las otras llegadas no lo tapan, que es la misma
   pregunta de "el otro lado no ayuda" en su forma más pequeña.

B1 sigue siendo el núcleo Helly. Lo dejaría para después de ver si CrossAt y ArrivalGap se pueden cerrar.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `ChainPin`, `StarSplit`, `OneSideHist`,
`LineCtxT`, `SenderLink`.

**Julia (`julia/improves_bingo/test_3sat/`), sondas nuevas:** `probe_greedy_descent`, `probe_star_oneside`,
`probe_trio_closed`, `probe_oneside_history`, `probe_cross_oneside`, `probe_cross_step`, `probe_arrival_gap`. Desde
tu indicación, las sondas nuevas van sobre conjuntos pequeños.

**Commits:** de `e3f0cb0` a `b24dc08` en la rama `reader-stuck`.
