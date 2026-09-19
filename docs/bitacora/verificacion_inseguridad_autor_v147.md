# Verificación para el Autor v147: la unión, partida por los caminos de sus ramas

Ricardo, soy Claude (Opus 5). Este informe sigue a v146 con el ataque a la distributividad del review
sobre la unión: primero `SideCover`, después las condiciones de soporte de las partes. El resultado: **el
veredicto depende de una sola afirmación sobre las uniones**: toda entrada de la unión revisada está en un
camino de una de las dos ramas.

Rama `spaik`, build de `AbsSat` (213 jobs), sin `sorry`, `[propext, Quot.sound]`. Commits `274c8a0`
(`JoinSide.lean`) y `d020af8` (`PartSplitReal.lean`).

---

## 1. Tu máquina original: la unión no se revisa

En `send_to_destine!` (`sat_machine.jl`) se hace el UP filtrado, se comprueba la validez y se hace
`impact!` en el destino: la unión, **sin review**. El review de la unión llega en el envío siguiente,
después de fijar los requisitos del próximo destino. Es exactamente la forma de `SupportSplit`: el review
de la unión de las dos ramas **ya fijadas**. El caso con fijaciones no es un caso aparte: es el caso.

**¿Habría que revisar tras cada unión?** No hace falta. Está demostrado (`WeakPairs.full_seq`, v144) que
revisar primero y después fijar y revisar da un estado encajado en los dos sentidos con fijar y revisar
directamente: el review solo quita lo que no está en ningún soporte, y un soporte que cumple las
fijaciones sobrevive igual por los dos caminos. Tu ahorro no abre ningún hueco.

## 2. `SideCover` (`JoinSide.lean`)

v146 redujo la cobertura de la partición a `SideCover`: cada entrada de la unión revisada tiene un ancla
arriba en un lado cuyas tablas la llevan.

* **Medido que la versión fuerte falla**: no toda ancla común está en el lado que lleva la entrada (476
  anclas cruzadas en K4, 406 en paridad). Hace falta la débil (existe una).
* **`sideCover_of_shared`** — `SideCover` solo tiene contenido en un caso: entrada de un solo lado con
  sus dos nodos presentes en ambos lados (1.044 de 56.780 en K4; 8.326 de 746.071 en paridad). Fuera de
  ahí, el ancla del review arriba ya está en el lado correcto por estructura.
* **`sideCover_of_sound`** — si las tablas de las dos ramas son exactas, `SideCover` se cumple: la entrada
  está en un camino real de su rama, el camino sobrevive a la unión y al review, y su nodo de arriba es el
  ancla.

**Medido**: `SideCover` sin excepción en **33,2 M entradas** (K4, paridad, prisma y 120 fórmulas
aleatorias; 37.895 uniones, ningún nodo de arriba compartido).

## 3. Las condiciones de soporte, desde los caminos (`PartSplitReal.lean`)

La partición pide, además de la cobertura, que cada parte sea un soporte dentro de su rama (once
condiciones). Todas salen de caminos:

* **`sup_through`** (sin hipótesis) — la relación *"estar en un camino de esta rama que sobrevive a la
  unión"* es por sí misma un soporte: el nodo del camino en cada paso es el vecino común, sus vecinos de
  abajo y de arriba son el padre y el hijo que piden las reglas, y el camino sobrevive a la unión y al
  review.
* **`splitOk_of_paths`** — por tanto, la partición completa sale de una sola cobertura: cada entrada de la
  unión revisada está en un camino de uno de los dos lados.
* **`supportSplit_of_paths`**, **`sat_of_paths`** — en todas las uniones de la ejecución, eso da
  `SupportSplit` y, con él, el veredicto.

> **`RunPaths`**: en cada unión que revisa la máquina, **toda entrada de la unión revisada está en un
> camino de alguna de las dos ramas fijadas**.

**Medido** (sonda `surv`): **615.911 entradas**, todas en un camino de alguna rama (K4, paridad, prisma).

Una versión más fuerte quedó descartada: exigir que cada rama explique todas las entradas que llevan sus
tablas falla (41.708 casos en paridad), porque una rama fijada puede quedarse sin caminos mientras la otra
sostiene la unión. También queda formalizada (`partSplit_of_realized`), como registro.

## 4. Cómo queda todo

| afirmación | hipótesis |
|---|---|
| toda respuesta (UNSAT, o SAT con certificado) es correcta | **ninguna** |
| revisar tras cada unión no cambia nada | **ninguna** (`full_seq`) |
| la partición de la unión, si cada entrada está en un camino de una rama | **ninguna** (`splitOk_of_paths`) |
| la máquina decide (veredicto) | **`RunPaths`** (construcción) o **`LivePinUp`** (lectura) |
| nunca responde "no sé" | `LivePinUp` |

`RunPaths` y `LivePinUp` son la misma dificultad desde los dos lados: la unión revisada no contiene nada
que no venga de un camino real de una de sus ramas.

## 5. Siguiente paso

Demostrar `RunPaths` por inducción sobre la ejecución: en cada unión, las ramas ya cumplen el invariante
(cada entrada de sus tablas que sobrevive está en un camino suyo), y hay que ver que el review de la unión
de las ramas fijadas no deja ninguna entrada fuera de esos caminos. Es el mismo núcleo que el nivel de
pares (v143), ahora con la estructura de la unión a favor: los nodos de arriba de las dos ramas son
distintos.
