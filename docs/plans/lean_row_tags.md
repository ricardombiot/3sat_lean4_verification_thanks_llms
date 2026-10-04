# Plan: las etiquetas por fila en Lean y el veredicto sin hipótesis (rama `row-tags`)

Espejo de `julia/improves_bingo` con `ROW_TAGS=on` (informes v204 §7 y v205). Objetivo:
`readerVerdictT φ = true ↔ Satisfiable φ` para la máquina con etiquetas, **sin hipótesis**.

## Arquitectura: una capa aparte, sin tocar `GPathB`

* `TGPath` = `GPathB` + etiquetas: `tags : List TagE`, con `TagE = (x, w, ℓ, a)` (el par, en cualquier orientación o
  reflexivo; la fila; la clave), y `krows`.
* Las operaciones etiquetadas son la operación de `GPathB` más la contabilidad de etiquetas:
  * `stampT`: la llegada;
  * `addNodeT`: la herencia de los padres;
  * `joinT`: la unión de etiquetas;
  * `filterAllT` y `reviewT = fuel (review ∘ tagRule)`.
* **Por qué aparte.** Las 12 000 líneas actuales no se tocan. `tagRule` solo borra, así que lo demostrado sobre
  `GPathB` (`Shrinks`, `AliveDocs`, contabilidad, solidez del lector) se reutiliza sobre la componente `GPathB`.

## La decisión matemática: estructuras descomponibles por filas

El v204 §7.4 decía «el núcleo etiquetado es la unión de los núcleos de las piezas». La forma precisa, y la que calcula
de verdad la regla, es esta:

> **`DecStruct`**: una estructura cerrada `(V, R)` tal que, **en cada fila `ℓ`**, toda pareja de `R` está en una
> subestructura cerrada de `(V, R)` que vive entera en **una** pieza de `ℓ` (todas sus parejas y nodos llevan la misma
> clave en `ℓ`).

No se pide una sola clave por fila para toda la estructura: eso sería elegir un camino de claves, y la regla no lo
calcula. Sí se pide que cada fila, por separado, se descomponga en piezas cerradas.

* **La regla lo calcula.** En su punto fijo, para cada `(ℓ, a)`, las parejas con `a` en `ℓ` forman una estructura
  cerrada, porque cada una pasó la comprobación con testigos de `a`. Así, el estado revisado es él mismo un
  `DecStruct`.
* **Lo conserva.** Una `DecStruct` sobrevive a la regla: cada pareja está en una pieza cerrada que la regla no toca.
  Es el análogo de `secStruct_review`.
* **Da la unión por construcción.** En la fila `n` del join, la cima `t` solo tiene aristas de su llegada. La
  subestructura de la pieza que contiene la pareja `(t, t)` vive en la pieza de su clave, que es la llegada. Así `t`
  está en el núcleo de su llegada fijada en `Q`.
* **Sin combinaciones entre filas.** Por eso el coste es polinómico.

## Fases

| fase | qué | criterio |
|---|---|---|
| T1 | `TGPath`, `stampT`, `addNodeT`, `joinT`, `tagRule`, `reviewT`, `advanceT`, `readerVerdictT` | compila; `#eval` en cnf pequeñas da el veredicto de Julia |
| T2 | `TagCarried`: la camarilla de una solución lleva su clave en cada fila; se conserva en todas las operaciones; `tagRule` la conserva | `machineVerdictT_of_sat`, completitud de la máquina |
| T3 | `DecStruct`/`DecKernel`; el estado revisado es `DecStruct` (`closedStateT`); `DecStruct` sobrevive a `reviewT` | análogos de `closedState_review` y `secStruct_review` |
| T4 | **`topUnion_of_dec`**: la unión por construcción en cada join | sin hipótesis |
| T5 | la inducción por la línea sobre `DecKernel` (bajada por filas nuevas de piezas, `LTUf`, `advance`) y el lector | `readerVerdictT_iff` sin hipótesis |

## Riesgos

* **R1** (T5): la bajada por las filas nuevas (`famStruct_rows_down`) tiene que conservar la descomposición por
  piezas. Se espera que sí, porque cada pieza baja como estructura cerrada, pero es donde puede aparecer trabajo
  nuevo.
* **R2** (T3): los enlaces a padres e hijos de la regla (`tag_link_support` en Julia) tienen que casar exactamente
  con los campos `node`, `par` y `son` de `FamStruct`.
* **R3**: el modelo en listas es lento; el `#eval` de T1 solo con cnf muy pequeñas.

## Estado (29-sept-2026)

* **T1 y T2 hechas** (commit `986b694`): la máquina con etiquetas en Lean y **`machineVerdictT_of_sat`**. La regla no
  pierde soluciones: la camarilla de una solución lleva su clave en cada fila (`TagCarried`), y ni la regla
  (`cliqueTags_tagSweep`) ni el corte (`carried_tagCut`) le quitan nada.
* **Problema encontrado al diseñar T3–T5 (deducido).** La descomposición por filas es **independiente por fila**. La
  inducción de la línea necesita más:
  1. en el join de arriba, la pieza de la cima (fila `n`, clave `a`) cae en su llegada;
  2. al bajar a esa llegada, la estructura tiene que volver a partirse en la fila `n−1` **dentro de la pieza `a`** y
     con los pins del lector.

  La regla solo garantiza que cada pieza `(n−1, b)` del estado entero es cerrada, no que lo sea su intersección con la
  pieza `(n, a)`. Pedir las intersecciones a lo largo de toda la bajada es pedir cadenas de claves, una por fila: son
  combinaciones entre filas, justo lo que las etiquetas por fila evitaban.
* **La sonda de Julia solo midió la fila del join** (`probe_row_tags_union.jl`: pieza de la fila `n` dentro de su
  llegada, 0 fallos). La §7.4 del v204, «la bajada respeta las etiquetas», era demasiado optimista.
* **Siguiente, antes de más Lean:** medir en Julia si las intersecciones de piezas de dos filas (`(n, a) ∩ (ℓ, b)`)
  son cerradas en los estados del lector fijados. Si no lo son, la regla por filas no basta para el veredicto.
