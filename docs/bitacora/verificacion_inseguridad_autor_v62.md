# Verificación para el Autor v62: la simetría — qué se demuestra, qué no, y por qué

Ricardo, soy Claude (Opus 5). Me pediste demostrar la simetría en longitud completa. **No la he demostrado.** Lo que he hecho es acorralarla: reforzar la evidencia, y demostrar en Lean que de las cuatro operaciones de la máquina **tres no pueden romperla** y exactamente **una** sí. Te cuento las dos cosas, y la segunda es la que vale.

---

## 1. Primero, intenté romperla

Antes de demostrar un enunciado, conviene atacarlo. Dos campañas nuevas, más grandes y con más variables:

| campaña | estados finales válidos | nodos | **violaciones de simetría** |
|---|---|---|---|
| v61 (tres semillas) | 64 | 3.849 | **0** |
| 60 casos, 90210, 3..6 vars | — | 3.432 | **0** |
| 40 casos, 777, 5..7 vars | — | 3.728 | **0** |
| **total** | | **11.009** | **0** |

No se rompe. El enunciado aguanta.

## 2. Dónde puede nacer la asimetría — y dónde no

La máquina hace cuatro cosas con la tabla de owners. Las miré una a una.

**`addNode` crea la propiedad simétricamente.** El nodo nuevo se lleva todos los owners globales, y —la línea que tu código comenta como `all_previous_nodes_are_owners_of_me!`— **todo nodo se lleva el nuevo**. Como un nodo es siempre owner global, las dos mitades encajan. Demostrado:

```lean
theorem OwnSymmetric_addNode (g) (d) (title)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hng : Ownership.NodesAreGowners g)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (addNode g d title)
```

**`filterRequire` no la toca.** Solo recorta la lista de owners globales; las tablas de los nodos quedan intactas. Demostrado (`OwnSymmetric_filterRequire`).

**`cleanInvalid` no puede romperla, pero no lo he demostrado.** Interseca la tabla de **todos** los nodos con la **misma** lista, así que la barrida completa quita un id de todas las tablas a la vez; y cuando un id sale de los owners globales, su propio nodo pierde la auto-posesión, falla `isValidNode` en su propio paso y desaparece. El argumento es sólido pero la barrida cambia los owners globales según va eliminando nodos, y esa contabilidad es un trabajo en sí misma. **Lo dejo dicho como argumento, no como teorema.**

**`reviewNode` sí puede romperla.** Interseca la tabla de un nodo con la unión de los owners de **sus propios vecinos**. Esa cantidad es por nodo, así que puede quitar `q` de `owners(p)` dejando `p` en `owners(q)`. **Es la única operación sin contrapartida simétrica.**

## 3. Lo que eso significa

Las 185 violaciones que v54 encontró en estados parciales **solo pueden venir de las pasadas de coherencia**. No de la construcción, no del pinchazo, y —salvo la contabilidad pendiente— tampoco de la barrida de inválidos.

Y eso deja la demostración de la simetría en longitud completa con una forma concreta:

> demostrar que, en un punto fijo del review sobre un grafo de longitud completa, **las asimetrías que las pasadas de coherencia introducen ya han desaparecido**.

Es un enunciado sobre el punto fijo, no sobre la construcción — exactamente la forma que v60 dijo que tenía que tener cualquier demostración aquí. No es la misma pregunta que antes: es más pequeña y está localizada en una sola operación.

## 4. Por qué no he ido más lejos

Intenté la demostración directa y no sale de los invariantes genéricos. La razón es precisa: una vez `reviewNode` quita `q` de `owners(p)`, **ninguna operación posterior quita `p` de `owners(q)` por sí sola** — las tablas solo encogen, y encogen por condiciones locales distintas en cada lado. Que al final coincidan es un hecho *semántico* (ambos lados significan «p y q están en un camino común»), no una consecuencia de las cláusulas de coherencia.

Dicho de otro modo: **la simetría es, como la exactitud de v60, una propiedad del punto fijo y no un invariante arrastrable.** No me sorprende, y es coherente con todo lo que hemos ido encontrando — pero prefiero decírtelo que venderte una demostración que no tengo.

## 5. Lo que sí queda en firme

- `OwnSymmetric_addNode` y `OwnSymmetric_filterRequire`, demostrados, cierre `[propext, Quot.sound]`.
- El enunciado, reforzado: **0 violaciones en 11.009 nodos**, cinco semillas, hasta 7 variables.
- La localización: **una sola operación** puede romperla, y está nombrada.
- Y lo de v61 sigue en pie: **bajo simetría**, `owners_contain_chain` y `chain_through_of_symmetric` dan que todo nodo está en un camino completo que posee entero — con la simetría como hipótesis explícita en el enunciado, no escondida.

## 6. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| Lector, pasadas de coherencia, `PickSome` ⟺ `Inhabited` | demostrados |
| Estado final exacto (semántico) | 0 zombis / 0 espurios (v60) |
| Simetría en el estado final | **0 de 11.009 nodos**, cinco semillas |
| **`addNode` conserva la simetría** | **demostrado** |
| **`filterRequire` conserva la simetría** | **demostrado** |
| `cleanInvalid` conserva la simetría | argumentado, no demostrado |
| `reviewNode` | **la única que puede romperla** |
| Simetría en longitud completa | **abierto** — propiedad del punto fijo |
| `owners_contain_chain`, `chain_through_of_symmetric` | demostrados **bajo** simetría |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 87 módulos, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
