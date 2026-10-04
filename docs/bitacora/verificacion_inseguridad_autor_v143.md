# Verificación para el Autor v143: fijar a la vez es fijar en secuencia

Ricardo, soy Claude (Opus 5). Este informe sigue tu lectura de las fijaciones: cada requisito obliga a
que todos los caminos parciales del conjunto pasen por un nodo (el valor del literal). Obligar a pasar
por `x`, después por `y` y después por `z` tiene que ser lo mismo que obligar a los tres a la vez.

Rama `spaik`, build de `AbsSat` (205 jobs), sin `sorry`, `[propext, Quot.sound]`. Módulo `SeqPin.lean`.

## 1. Medido primero

Sonda `helly seqpin`: en cada envío de la ejecución con dos o más fijaciones se compara
`filterAllAgg w rq` (todas a la vez) con fijar una a una revisando tras cada una.

| familia | envíos con ≥2 fijaciones | ambos válidos | tablas idénticas | validez distinta |
|---|---|---|---|---|
| K4 | 553 | 100 | 100 | 0 |
| paridad | 259 | 134 | 134 | 0 |
| prisma | 861 | 172 | 172 | 0 |
| K3,3 | 861 | 208 | 208 | 0 |

## 2. Demostrado

| teorema | enunciado |
|---|---|
| `seq_eq_all` | desde un estado con contexto de lector, si fijar a la vez da un estado válido, fijar en secuencia también, y cada resultado está dentro del otro (`Embedded` en los dos sentidos) |
| `chainSound_of_embedded` | un camino de `B` es un camino de cualquier estado que contenga a `B` |
| `tablesSound_of_embedded` | con encaje en los dos sentidos, la exactitud pasa de uno a otro |
| `multiPinExact` | sobre un estado de lector válido y exacto, fijar varios nodos a la vez lo deja exacto si **una** fijación lo hace (`ReaderPinExact`) |
| `multiPinExact_of_pairs` | y con el nivel de nodos (v142) basta el nivel de **pares** (`PairPinExact`) |

La idea de la prueba es tu diseño visto como punto fijo: las tablas de cada resultado son un soporte
dentro del estado de partida que ya lleva todas las fijaciones, y un soporte así sobrevive a cualquier
fijación compatible y a todo el review (`AOk_filterAllAgg`). Cada resultado sobrevive, por tanto, a las
fijaciones del otro.

## 3. Qué cambia y qué no

* **Cambia**: para los estados del lector, varias fijaciones no cuestan nada más que una. Lo abierto es
  solo `PairPinExact` —una fijación, entradas entre dos nodos distintos—.
* **No cambia todavía**: `GhostsLine` parte de `filterWeakAll kv.2 ws`, que no es un estado de lector
  (lleva los requisitos débiles y no pasó por `filterAllAgg`). `seq_eq_all` sí vale ahí si ese estado
  tiene contexto de lector (`RCtx`, `SMP`, `PMS`, `SN`), pero la primera fijación sobre él no la cubre
  `ReaderPinExact`. El paso siguiente es enunciar el nivel de pares para ese estado de partida, y así
  reducir también `GhostsLine` a una fijación.
