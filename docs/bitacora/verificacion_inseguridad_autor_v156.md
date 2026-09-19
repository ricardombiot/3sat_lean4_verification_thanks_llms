# Verificación para el Autor v156: la etapa de variables queda demostrada

Ricardo, soy Claude (Opus 5). He hecho los dos pasos que acordamos: partir `PinJoin` en sus dos etapas y
demostrar la de variables. El veredicto depende ya solo de la etapa de cláusulas.

Rama `spaik`, build de `AbsSat` (227 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Commit
`625c80e`. Módulo nuevo: `PinVar.lean`; ajustados: `PinHistory.lean`, `PinSend.lean`. Sonda nueva:
`helly unionfix`.

---

## 1. La cadena del veredicto

```
veredicto ⇐ PinCommutes1 ⇐ PinAdvance ⇐ PinJoin ⇐ PinJoinVar ∧ PinJoinClause
                                                    ✔ demostrado   ✘ abierto
```

`sat_of_pinJoinClause`: el veredicto bajo `PinJoinClause` sola.

## 2. Paso 1: `PinJoin` por etapas

* `PinAdvance` y `PinJoin` se enuncian ahora sobre **ramas** de la máquina, no sobre líneas cualesquiera. Es
  lo que la inducción usa, y la etapa de variables solo es cierta para estados que la máquina construye.
* `PinJoinVar`: uniones con la cima antes del último paso de literal. `PinJoinClause`: el resto.
  `pinJoin_of_stages` las junta.

## 3. Paso 2: la etapa de variables, sin hipótesis (`PinVar`)

| pieza | resultados | contenido |
|---|---|---|
| A. las ramas no pierden caminos | `branch_carries`, `branch_line_complete`, `branch_send_complete`, `branch_send_chain` | cada estado de una rama, y cada envío suyo, contiene todos los caminos genuinos que respetan sus fijaciones (adaptación de la conservación de v148 a las ramas) |
| B. la etapa de variables es exacta | `adv_sound_var`, `branch_sound_var` | allí ningún envío va a una fila, así que todos salen gratis |
| C. el pegado | `sel_local`, `sel_det`, `glue_agree`, **`var_glue`** | en la etapa de variables, el nodo de cada paso depende de una sola variable. Si x↔v, x↔r y v↔r están cada uno sobre un camino, la asignación que toma el valor de r en su variable y el resto del camino de x↔v pasa por x, por v, por r, por la clave y por las fijaciones de la rama |
| D. montaje | **`pinJoinVar`** | ese camino es un camino del envío fijado de un lado, y de ahí la unión fijada cabe en cualquier estado que contenga los lados |

Es tu idea en la etapa donde ya se puede escribir sin hipótesis: el UP añade un paso a todos los caminos
parciales (A), y el valor fijado quedó fijado cuando su variable era clave (la rama).

## 4. Medidas nuevas

| sonda | resultado |
|---|---|
| `unionfix` | **sin fijar nada, la unión por clave ya es un punto fijo del review** (98 uniones, 0 cambios), aunque trae entradas de otros lados (24 / 440 / 114). Todo el trabajo del review lo provoca la fijación |
| `pincommute` aleatorias (profundidad 2) | 3 semillas × 20 fórmulas: 27,3 M de entradas, **0 violaciones** |
| `pinjoin` aleatorias | 35.370 fijaciones, **0** |

## 5. Lo que queda: `PinJoinClause`

La misma afirmación en la etapa de cláusulas. El argumento de C falla allí por una sola razón: la fila de
una cláusula depende de **tres** variables, así que cambiar el valor de la variable fijada puede cambiar
la fila elegida, y con ella las cláusulas que se cumplen. El pegado tiene que elegir también las filas.
Ahí entran tus filas como nodos: la fila que ya está en los caminos de x↔r (o de v↔r) es la candidata.
Es el siguiente punto que ataco.
