# Informe — Mapa bin (`julia/improves_bin`): errores encontrados y soluciones aplicadas

> Rama `improves_bin`. Implementación del mapa binario con ventana prohibida `(0,0,0)`
> (docs/plans/bin-map.md), fases A–D. Este informe recoge los errores que aparecieron durante la
> implementación, su causa raíz, cómo se detectaron y la solución aplicada.

## Resumen

| # | Error | Fase | Detectado por | Síntoma |
|---|---|---|---|---|
| 1 | `get_ids_last_step` no enlaza el fusión raíz | A | test unitario | fusión raíz sin hijos; test semántico daba `false` en asignaciones SAT |
| 2 | `round(x, 2)` posicional en el harness | D | ejecución del harness | `MethodError: round(::Float64, ::Int64)` |
| 3 | Falso positivo UNSAT (gpath "avanza" vacío) | D | harness diferencial | 6 fórmulas UNSAT daban `SAT` con 1 solución inválida |
| 4 | Nodo muerto en gpath SAT (review no repasa) | D | harness diferencial | `GRAVE ERROR READER` al extraer soluciones de 2 fórmulas SAT |

Los cuatro están corregidos y verificados. Siguen los detalles.

---

## Error 1 — El fusión raíz no se enlaza con la variable 1

**Síntoma.** En el mapa bin, el test semántico (`chain_exists`) devolvía `false` para 6 de las 8
asignaciones de `bin_v3_c2.cnf`, cuando debería dar `true` para 7 de ellas.

**Causa raíz.** `get_ids_last_step` se copió del mapa clásico con la condición `gmap.step - 1 > 0`.
En el clásico eso es correcto porque el paso 0 es la primera variable (sin padres). Pero en el mapa
bin el paso 0 es el **fusión raíz**, que sí debe poder enlazarse con la variable 1 (paso 1). Al usar
`> 0`, `get_ids_last_step` devolvía el conjunto vacío para `step == 1`, y la variable 1 quedaba sin
padre (`root.sons` vacío).

**Solución.** En `graph_map_bin.jl`, cambiar la condición a `gmap.step > 0` (el paso 0 debe poder
enlazarse), con un comentario explicando la diferencia respecto al clásico.

**Detección.** El test unitario `test_graph_map_bin.jl` (bloque "semántica", `chain_exists`) lo cazó
de inmediato, validando el valor de esa prueba.

---

## Error 2 — `round(x, 2)` en vez de `round(x, digits=2)`

**Síntoma.** El harness `compare_bin.jl` abortaba al imprimir el resumen.

**Causa raíz.** En Julia, el segundo argumento posicional de `round` es un `RoundingMode`, no el
número de dígitos. `round(a.t, 2)` falla; hay que usar `round(a.t, digits=2)`.

**Solución.** Cambiar `round(x, 2)` por `round(x, digits=2)` en `compare_bin.jl`.

**Detección.** Primera ejecución del harness (fallo de arranque inmediato).

---

## Error 3 — Falso positivo en fórmulas UNSAT

**Síntoma.** En 6 fórmulas UNSAT del corpus (p. ej. `v6_c26_i6`, `v6_c26_i12`), el mapa bin devolvía
`SAT` con 1 solución inválida (`checker=MAL`). El exhaustivo y el mapa clásico decían `UNSAT`.

**Causa raíz.** En `do_up!` / `add_row!`: cuando la ventana prohibida elimina el **único** candidato
de un paso de cláusula, `group_parents_by_shifted_id` devuelve vacío y `add_row!` no crea ningún nodo,
pero **no marcaba el gpath como inválido**. El gpath "avanzaba" de paso sin añadir nodos, manteniendo
`is_valid = true`, hasta llegar al final con pasos vacíos (se vio: pasos 79–92 ausentes en
`v6_c26_i6`). El mapa clásico nunca tiene este caso (sin ventanas prohibidas, siempre hay candidato),
así que el bug es exclusivo del bin.

**Solución.** En `add_row!`, si `group_parents_by_shifted_id` devuelve vacío, marcar
`gpath.is_valid = false`; y en `do_up!`, re-comprobar `gpath.is_valid` después de `add_row!` antes de
avanzar el paso.

**Detección.** El harness diferencial (Fase D), comparando veredicto/soluciones clásico vs bin vs
exhaustivo. Tras el fix, `v6_c26_i6` pasó de `SAT (1 solución inválida)` a `UNSAT`.

---

## Error 4 — Nodo muerto en el gpath de soluciones SAT

**Síntoma.** En 2 fórmulas SAT (`v4_c12_i1`, `v4_c12_i9`), el veredicto era correcto (`SAT`), pero el
lector exponencial lanzaba `GRAVE ERROR READER... GPATH INVALID.` al extraer las soluciones.

**Causa raíz.** El review corre en `filter!` **antes** de `add_row!`. En ese momento, un nodo de la
rama "mala" (p. ej. `var1=1` = asignación "1111", que viola una cláusula) está todavía en el último
paso y es válido (no necesita hijos). Después, `add_row!` salta su ventana prohibida y ese nodo se
queda **sin hijo**, pero `review_owners` ya quedó en `false`, así que el review no vuelve a correr para
podarlo. El nodo muerto sobrevive en el gpath final.

**Solución.** En `group_parents_by_shifted_id`, al saltar una ventana prohibida, marcar
`gpath.review_owners = true` para que el review vuelva a correr y pode el padre que se quedó sin hijo.

**Detección.** El harness diferencial (Fase D). Tras el fix, `v4_c12_i1` y `v4_c12_i9` producen
exactamente las soluciones del exhaustivo (`["0011","0111"]` y `["0011"]`).

---

## Estado

- Tests unitarios en verde: `GraphMapBin` 54/54, `GraphMap` (clásico) 34/34.
- Los cuatro errores están corregidos y verificados.
- **Harness diferencial (`compare_bin.jl`) en verde**: 73 instancias, **73/73 mismo veredicto,
  73/73 mismas soluciones (lector exponencial), 0 fallos de checker**, clásico == bin == exhaustivo.
  La única instancia saltada es `simple_v3_c2.cnf` (2-SAT, rechazado por el importador por diseño).

## Nota de rendimiento (prevista, no bloqueante)

El mapa bin triplica los pasos de cláusula (`m → 3m`), así que es más lento que el clásico
(~7× en `v8_c10`, ~25× en `v4_c20`). Es el coste anticipado en v187 §5 y en el plan §7, no un bug.
