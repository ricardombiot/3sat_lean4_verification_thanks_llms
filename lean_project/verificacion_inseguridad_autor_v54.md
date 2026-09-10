# Verificación para el Autor v54: la ruta C, atacada — el residuo se reduce al descenso

Ricardo, soy Claude (Opus 5). Atacar la ruta C significaba **medir antes de demostrar**, y las mediciones han dicho más de lo que esperaba: una vía se cierra, y el problema abierto se reduce a un enunciado *local, de un solo paso y en una sola dirección*.

---

## 1. La simetría de la propiedad: refutada, y con precisión

`Threaded.threaded` da, para todo nodo `a`, **una cadena completa cuyos nodos poseen todos a `a`**. El residuo pide lo contrario: que `a` tenga un *owner* en cada paso. Con simetría (`q ∈ owners(p) ↔ p ∈ owners(q)`) los dos enunciados serían el mismo, y la cadena que `threaded` ya construye sería el testigo.

`lake exe extend --randomsym`, 40 instancias, 3.808 estados válidos, 116.330 nodos:

| | |
|---|---|
| violaciones de simetría | **185** |
| de ellas, en un par **enlazado** | **0** |
| de ellas, a distancia **≥ 2** | **185** |
| de ellas, tocando el paso 0 | 24 |
| violaciones tras **otro `review`** | **185** |

Tres cosas de golpe: la simetría es **falsa**; falla **exactamente donde vive el residuo** (distancia ≥ 2, nunca en pares enlazados — ahí el puente de v39 la garantiza); y **no es una propiedad de punto fijo**, porque otro `review` no elimina ni una. **Vía cerrada.** Sin la medición habría invertido semanas en demostrarla.

## 2. La cadena que `threaded` construye, ¿es ya `PairwiseOwned`?

Es la pregunta constructiva: si lo fuera, el objetivo dejaría de ser un existencial sobre todas las selecciones y pasaría a ser un **invariante de la escalada** — la forma que `hop_up`/`hop_down` ya tienen, y que este proyecto sabe demostrar.

`lake exe extend --randomthread`, escalada golosa (el primer hijo que posee el ancla):

| campaña | anclas | cadena construida | **`PairwiseOwned`** |
|---|---|---|---|
| 8 casos, 2026, 3..5 vars | 7.586 | 7.586 | 7.558 |
| 12 casos, 31337, 3..6 vars | 26.075 | 26.075 | 25.626 |

**La escalada golosa nunca se atasca** (0 de 33.661) pero su cadena **no siempre** es co-poseída: 477 fallos. No es una refutación de nada — `SupportedAt` es un existencial y esto solo dice que *esa* regla falla.

## 3. `SupportedAt`, medido por búsqueda: cero zombis

Para cada ancla cuya cadena golosa falla, búsqueda en profundidad sobre **todas** las cadenas que pasan por ella, conservando solo candidatos enlazados padre→hijo y mutuamente poseídos con el ancla y con todo lo ya elegido.

| campaña | estados válidos | anclas | golosa OK | **búsqueda encuentra** | presupuesto agotado | **NO existe cadena (zombi)** |
|---|---|---|---|---|---|---|
| 8, 2026, 3..5 | 472 | 7.586 | 7.558 | 28 | 0 | **0** |
| 12, 31337, 3..6 | 1.069 | 26.075 | 25.626 | 449 | 0 | **0** |
| 10, 4242, 4..6 | 834 | 22.177 | 21.763 | 414 | 0 | **0** |
| **total** | **2.375** | **55.838** | 54.947 | **891** | **0** | **0** |

**55.838 anclas, cero zombis, y el presupuesto de búsqueda no se agotó ni una vez.** Es la primera medición *directa* de `SupportedAt` sobre mapas derivados de CNF reales — `l6search` solo lo hacía sobre mapas sintéticos. Lo que falla es **la regla de elección**, no el enunciado.

## 4. La medición que lo cambia todo: goloso **con historia**

Entre «goloso ciego» y «búsqueda con backtracking» está la regla que una demostración querría: goloso que además conserva compatibilidad con todo lo ya elegido, y que **nunca retrocede**.

`lake exe extend --randomhist`:

| campaña | anclas | **atascos bajando** | **atascos subiendo** | cadena completa y co-poseída |
|---|---|---|---|---|
| 8, 2026, 3..5 | 7.586 | **0** | **0** | 7.586 |
| 12, 31337, 3..6 | 26.075 | **0** | 4 | 26.071 |
| 10, 4242, 4..6 | 22.177 | **0** | 3 | 22.174 |
| **total** | **55.838** | **0** | **7** | **55.831** |

Dos hechos, y el segundo es el importante:

- Añadir la historia baja los fallos de **891 a 7**. La regla de un paso casi basta.
- **Bajando no se atasca nunca: 0 de 55.838.** Los siete atascos son todos **subiendo**.

Y esa asimetría tiene una explicación que encaja con tu diseño: **la máquina construye hacia arriba**. En cualquier estado, el pasado está completamente podado y el futuro no. Descender es caminar por territorio ya filtrado; escalar es apostar sobre lo que aún no lo está.

## 5. El residuo, reducido

`Verdict.lean` ya decía algo que ahora vale su peso en oro: **`Inhabited` no necesita `Supported`**; necesita `SupportedAt` **en un nodo a tu elección**. Elige uno del paso más alto y desciende.

| campaña | anclas en el paso alto | cadena completa co-poseída |
|---|---|---|
| 8, 2026, 3..5 | 657 | **657** |
| 12, 31337, 3..6 | 1.673 | **1.673** |
| 10, 4242, 4..6 | 1.389 | **1.389** |
| **total** | **3.719** | **3.719/3.719** |

Así que el objetivo pasa de esto:

> `Supported`: **todo** nodo está en **alguna** cadena completa co-poseída. *(existencial anidado, ambas direcciones, refutado en su forma golosa)*

a esto:

> **`DownH`** — en un punto fijo de `review`, si `a` es un nodo con `a.step > 0` y `S` un conjunto de nodos que se poseen mutuamente entre sí y con `a`, entonces `a` tiene un **padre** que se posee mutuamente con todo `S ∪ {a}`.

Un enunciado **local, de un paso, universal y en una sola dirección**. Es exactamente la forma que `Threaded.hop_down` ya tiene demostrada —da un padre que posee *el ancla*— reforzada a «posee *toda la historia*». Y con él, por inducción sobre el paso (que es como está escrito `extendDownTo` en `Extendable.lean`), sale `SupportedAt` en el nodo alto, y con él `Inhabited`, y con él el veredicto.

## 6. Lo que esto **no** es

- **Es medición, no demostración.** `DownH` está sin demostrar; lo que hay son 55.838 anclas sin un solo atasco bajando.
- **La regla golosa es una regla concreta** —el primer padre de la lista— y los 7 atascos subiendo prueban que la misma regla *no* es completa en la otra dirección. Cualquier demostración tiene que ser sobre el descenso, no sobre la escalada.
- **No toca la complejidad.** Sigue sin un solo teorema.
- El tamaño de las instancias es el de siempre (3..6 variables); es el rango donde el arnés diferencial corre en tiempo razonable.

## 7. Estado

| | |
|---|---|
| Mitad de completitud (ley de conservación, driver incluido) | cerrada |
| S1 — un camino leído es una solución | cerrado |
| S2 — conjunto vacío ⟹ UNSAT | cerrado |
| Simetría de la propiedad | **refutada** (185/116.330, todas a distancia ≥ 2) |
| Cadena golosa co-poseída | falso (891/55.838) |
| `SupportedAt` por búsqueda | **0 zombis en 55.838 anclas** |
| Goloso con historia, **bajando** | **0 atascos en 55.838** |
| Goloso con historia, subiendo | 7 atascos |
| **`DownH`** — el nuevo objetivo | abierto, local, de un paso |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 84 módulos, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
