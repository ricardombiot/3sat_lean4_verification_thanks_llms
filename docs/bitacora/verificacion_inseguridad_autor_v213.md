# Verificación para el Autor v213: el lector por caminos, la revisión y `ChainInv` sin B1

Ricardo, este informe sigue al v212 (sesión del 29 al 30-sept-2026, rama `reader-stuck`). El v212 terminaba con la
"espina": una camarilla que se construye sin retroceso. Me preguntaste si se podía diseñar un lector sin retroceso a
partir de todo lo demostrado. Aquí cuento lo que salió:
* un **lector por caminos de documentos**, prototipado en Julia, que lee sin retroceso las 28 instancias SAT probadas;
* **tu corrección**: la revisión tras cada elección es imprescindible. Sin ella la espina se atasca; con ella, nunca;
* **`ChainInv` demostrado en toda la línea sin B1**. Es la propiedad que garantiza que, con revisión, cualquier
  elección del lector por caminos sirve;
* lo que queda: el **primer pin** y **`SibStarInv`**. Los dos se cumplen siempre en lo medido, y los dos son el mismo
  acuerdo entre dos ramas, ahora en su forma más pequeña.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * **`chainInv_run`** (`ChainLine.lean`): `ChainInv` en todas las entradas finales bajo `SibStarInv` + `ArrHole` +
    `AbsHole`. Sin B1 ni `StarJoinDown`;
  * **`carried_of_spine`**: en un estado cerrado, una cadena completa de padres vecinos dos a dos es una camarilla;
  * el **lema de los dos hermanos** (`two_helly`, `parent_for_chain`) y el **paso forzado con un padre**
    (`forced_parent`);
  * `LinksInv` en toda la línea sin hipótesis (`line_linksInv`).
* **Refutado por medida:** mi primera formalización de la espina sin revisión (`SpineTrio`) es falsa en `clause_mix`.
* **Abierto, con 0 fallos medidos:** `SibStarInv` y el primer pin del lector.

---

## 1. El lector por caminos, sin retroceso (`probe_pathreader.jl`, `be846f7`)

Tres lectores sobre el mismo estado final, todos **sin retroceso** (pediste esto explícitamente): toman siempre el
primer candidato y, si falla, cuenta como fallo.

| lector | cómo elige | correctos (28 SAT) | atascos | tiempo total |
|---|---|---|---|---|
| por colores (el actual) | de abajo arriba, fija un color y revisa | 28 | 0 | 1,3 s |
| **por caminos** | de arriba abajo, fija una cima y luego un padre del último fijado, y revisa | 28 | 0 | 20,5 s |
| espina | de arriba abajo, el primer vivo vecino de todo lo elegido, sin revisión | 28 | 0 | 0,007 s |

Los dos lectores nuevos bajan siempre por padres. El lector por caminos es lento porque revisa el estado entero en
cada paso; el prototipo no está optimizado.

Sobre tu idea de buscar las camarillas completas por análisis de grafos: una solución es una camarilla con un nodo
por paso, y la espina es justamente esa búsqueda. En un grafo cualquiera eso exige retroceder. Lo que medimos es que
en los estados que deja la máquina no hace falta, porque la revisión ya ha podado lo incompatible.

## 2. La espina en Lean, y por qué hay que revisar (`9f67bcc`, `7d1848a`)

Formalicé primero la espina **sin revisión** (`Spine.lean`, `SpineZombie.lean`, `SpineVerdict.lean`):
* **`forced_parent`**: en un estado cerrado, si un nodo tiene un único padre vivo, ese padre es vecino de todo lo que
  es vecino del nodo. Sale del campo de padres de `ClosedState`.
* **`two_helly`**: subconjuntos no vacíos de un conjunto de dos elementos que se cortan dos a dos comparten un
  elemento. Con como mucho dos padres (medido: nunca hay tres), el acuerdo con todo lo elegido se reduce a tríos
  (**`parent_for_chain`**).
* **`carried_of_spine`**: una cadena completa es una estructura cerrada fijada en todos los pasos, y por tanto una
  camarilla (`carried_of_pinned`).
* **`readerVerdict_iff_of_spine`**: el veredicto del lector actual bajo `TwoParents` + `SpineTrio`, sin hipótesis
  sobre joins ni llegadas.

Al medir las hipótesis en los estados que visita el lector (`probe_spinehyps.jl`, 28 instancias, 351 estados):
* `TwoParents` se cumple siempre;
* **`SpineTrio` es falsa**: con elecciones al azar, la espina sin revisión se atasca en `clause_mix`, en el estado
  final y en uno fijado, aunque otra elección sí llega. Mi sonda anterior no lo vio porque solo probaba las dos
  opciones en el primer paso atascado.

**Tu observación lo explica: siempre hay que revisar.** La revisión tras cada elección poda los nodos incompatibles,
y eso es lo que garantiza que cualquier elección lleve a una solución. Con revisión, **el lector por caminos hizo
1 620 lecturas con 2 156 elecciones al azar y no se atascó nunca**, `clause_mix` incluida.

`readerVerdict_iff_of_spine` es un teorema correcto, pero con una hipótesis falsa; está anotado en los ficheros.
Siguen valiendo `carried_of_spine`, `forced_parent` y `two_helly`.

## 3. Con revisión, "cualquier elección sirve" es `ChainInv`

`ChainInv u` dice: en una estructura cerrada fijada (un nodo por paso) desde la cima, cualquier nodo se puede fijar
también sin vaciarla. Aplicado al lector por caminos:
* el estado tras fijar una cadena desde la cima es una estructura cerrada fijada desde arriba;
* por `ChainInv`, cualquier padre vivo $p$ se puede fijar: hay una subestructura cerrada con $p$ fijado;
* esa subestructura concuerda con todas las fijaciones, así que sobrevive a la revisión (`secStruct_review`), y el
  nuevo estado es válido;
* en el paso 0, el estado tiene un nodo por paso y es cerrado: `carried_of_pinned` da la camarilla.

## 4. `ChainInv` sin B1 (`ChainSide.lean`, `LineCtxL.lean`, `ChainLine.lean`, `d9e1c5a`)

* **Join, `chainInv_join_oneSide`** (demostrado). Una estructura fijada desde la cima tiene una sola cima $t$ y cabe
  en su estrella. `StarOneSide` en el lado de $t$, que sale de los huecos (`oneSide_holes`), la hace de ese lado
  (`pinned_side`), y se aplica el `ChainInv` del lado. **Sin `StarJoinDown`.**
* **UP, `chainInv_up_sib`** (demostrado). El paso de subir solo necesita `StarInv` del remitente en estructuras cuyas
  cimas son **hermanos**: los padres de una misma cima, con el mismo id y el mismo padre. Esa es la hipótesis
  **`SibStarInv`**. Que la estructura que baja es de hermanos está demostrado.
* **Montaje.** La inducción de la línea no dejaba al paso UP saber que el remitente es una entrada de la línea, así
  que no se podía usar allí una hipótesis sobre esas entradas. `LineCtxL.lean` copia la inducción con un paso UP que
  recibe la pertenencia (`run_provL`). `LinksInv` de los árboles de llegadas sale sin hipótesis (`tree_links`).
* **`chainInv_run`**: `ChainInv` en todas las entradas finales, bajo **`SibStarInv` + `ArrHole` + `AbsHole`**.

## 5. Lo que queda: el primer pin y `SibStarInv` (`probe_sibstar.jl`, `92c6b85`, `8d28e3c`)

**El primer pin.** `ChainInv` cubre todas las elecciones del lector *después* de fijar la primera cima. Fijarla en el
estado final entero sin vaciarlo es `StarInv` del estado entero. Al bajar un nivel, esa estructura tiene las cimas de
las dos llegadas del remitente, así que mezcla ramas: es B1. Medido: 0 fallos (1 565 entradas de la línea y 13
estados finales).

**`SibStarInv`.** Medido: 0 fallos (1 565 estructuras de hermanos y 907 al azar). Con una sola cima,
`pinned_side` lo demuestra; con dos hermanos no, porque un testigo puede estar en la estrella de un hermano y no en la
del otro. Los dos hermanos vienen de abuelos distintos, es decir, de las dos ramas del nivel de abajo.

**Con la lente de los requisitos** (6 603 testigos, 100 %): cuando la restricción a la estrella de $t_1$ corta una
pareja, sus testigos de fuera
* no los posee ningún padre de $t_1$,
* están en la estrella del hermano $t_2$, y
* **no poseen ningún nodo del color del abuelo de $t_1$**.

Restringir a la estrella de $t_1$ equivale, en primer orden, a **fijar el color del abuelo de $t_1$**, y una
estructura fijada así ya es de un solo lado (`pinOneSide2`, v212). `SibStarInv` se reduce a "fijar el color del
abuelo conserva $z$–$t_1$": la misma forma de siempre, en su versión más pequeña, dos hermanos y un pin.

## 6. Dónde estamos

| pieza | estado |
|---|---|
| lector por caminos con revisión | prototipo: 28/28 sin retroceso; con elecciones al azar, 0 atascos en 1 620 lecturas |
| `ChainInv` en toda la línea | **demostrado** bajo `SibStarInv` + `ArrHole` + `AbsHole` |
| `ArrHole`, `AbsHole` | 0 fallos medidos; 99,4 % de `ArrHole` explicado por los requisitos del destino (v212) |
| `SibStarInv` | 0 fallos; equivale a "fijar el abuelo conserva la pareja" en estructuras de dos hermanos |
| primer pin | 0 fallos; es B1 para el estado entero |
| el lector por caminos en Lean | falta definirlo y conectarlo con `ChainInv` y `carried_of_pinned`; es trabajo de montaje |

Todo lo que queda abierto es el mismo acuerdo entre dos ramas, del que el v211 y el v212 ya contaban. Lo nuevo es que
ahora tiene su forma mínima: dos hermanos, que vienen de abuelos distintos, y un pin.

**Mi recomendación:** volver al núcleo con una idea nueva en vez de afinar las mismas herramientas. Una candidata que
sale de este informe es el **orden** en que lee el lector. El lector actual fija colores de abajo arriba; el nuevo fija
caminos de arriba abajo, y justo el primer pin arriba es donde aparece B1. Merece la pena medir si un lector que
empieza por abajo (fijar la raíz y subir por hijos) evita el primer pin, o lo traslada a otro sitio.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `Spine`, `SpineZombie`, `SpineVerdict`,
`ChainSide`, `LineCtxL`, `ChainLine`.

**Julia (`julia/improves_bingo/test_3sat/`), sondas nuevas:** `probe_pathreader`, `probe_spinehyps`, `probe_sibstar`.

**Commits:** de `be846f7` a `8d28e3c` en la rama `reader-stuck`.
