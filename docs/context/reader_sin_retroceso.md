# Traducción: qué debe cumplirse en la máquina para que el reader sin retroceso funcione

> Verificado contra `lean_project/AbsSat/GraphPath/Model/` y los informes v183–v193.
> Cada pieza va marcada como **demostrado**, **medido**, **deducido**, **propuesto** o **abierto**.

## 0. Qué es "que el reader funciona"

El reader es `ReaderExec.readerVerdictW` (`ReaderExec.lean:59`). Recorre las **entradas de la corrida**
de la máquina (`pureRunW φ`, la traza entera, no solo estados finales — `PureDriverImproves.lean:80`)
y, para cada `kv`, aplica el lector a `filterAllAgg kv.2 []`. El lector (`readLoop`, `ReaderExec.lean:46`)
toma el primer paso con elección (`firstChoice`), pincha la primera entrada viva cuyo filtro deja el
grafo válido, y **nunca deshace**. Devuelve SAT si alguna entrada termina.

Se parte en dos:

- **Solidez** (`readerVerdictW_sound`, `ReaderExec.lean:149`): si el reader termina, `φ` es
  satisfacible. **Demostrada, sin hipótesis abiertas** (solo la buena formación `WF φ`). La cadena en
  la que aterriza es un modelo.
- **Completitud**: si `φ` es satisfacible, el reader **no se atasca**. Es `ProgressAgg g₀`
  (`ReaderExec.lean:168`): *en todo estado alcanzable, todo paso con elección tiene alguna entrada viva
  cuyo pin deja el grafo válido*.

**Demostrar que funciona = demostrar que no se atasca.** Lo demás ya está.

## 1. Vocabulario

- `GPathM`: `nodes`, `gowners` (**la global**: entradas vivas), `current_step` (`GPathM.lean:50`).
- Tabla de un nodo: `PNodeM.owners`; `w ∈ tabla(x)` = "`x` posee a `w`".
- `ownersAt g.gowners k`: entradas vivas de la global en el paso `k` (`GPathM.lean:70`).
- `choiceAt g k`: hay **≥2 ids de mapa distintos** entre las entradas de la global en `k`
  (`PickInduction.lean:162`).
- **Cadena** (`ChainSound g sel`): un nodo vivo por paso, enlazado por padres, mutuamente poseídos y
  autoposeídos (`Review.lean:87`). Denota una solución.
- **Pinchar `q`**: `filterAllAgg g [q.id]`. Con `X = filterWeak g (q.step,[q])` y `C = cleanPair X`.

## 2. La condición más corta (ruta `PinAlive`)

**`PinAlive`** (`PinAliveChain.lean:84`):

> En todo estado válido con su contexto (`DCtx`), pinchar cualquier entrada viva de la global **deja el
> grafo válido**.

De ahí, por la inducción del descenso (`chained_of_pinAlive`, `PinAliveChain.lean:102`):

> **`OwnerChained g`** (`ReaderChain.lean:1201`): toda entrada viva de la global está en alguna cadena.

y el reader nunca puede elegir un nodo sin camino (`pinReachable_of_ownerChained`, `ReaderChain.lean:1213`),
así que el veredicto sale (`readerVerdictW_of_pinAlive`, `PinAliveChain.lean:190`).

- **Medido, sin fallos**: 1.016/1.016 y 12.602/12.602 pinchazos (`PinAliveChain.lean:81-83`).
- **`PinAlive` sigue siendo la hipótesis abierta** de esta ruta; no está descargada.

## 3. La escalera descompuesta (una obligación por pin)

En cada pin (estado `g`, paso elegido `k`, entrada viva `q`), con `X = filterWeak g (q.step,[q])` y
`C = cleanPair X`:

| peldaño | qué debe cumplirse en la máquina | estado |
|---|---|---|
| **`PairExact g`** (`OneStep.lean:859`) | Toda entrada **viva** de una tabla, `w ∈ tabla(x)` con `w` vivo, está en una cadena de `g` que pasa por `x` **y** por `w`. | medido 0 fallos |
| **`KeptOwnUp/Down`** (`OneStep.lean:1091`) | En `C`, cada tramo tiene un testigo `w` que ya lo era en `g` (`WitUp`), que en `g` posee un nodo vivo `p` del paso pinchado (`p.id = qid`), y que está en la **tabla de `C` de todos los miembros**. | medido: todo tramo tiene alguno |
| **`CleanRest X`** (`PairHelly.lean:231`) | *Si* tras `cleanPair X` vale `SegGood`, *entonces* vale todo `PStateG` (el armazón: `NodupIds`, `I1`, `I1s`, tablas vivas, autoposesión, `NotRoot`, etc.). Es una **implicación**, no una lista. | medido 0 fallos |
| **`LaterValid X`** (`PinDoomed.lean:75`) | Las vueltas de limpieza posteriores a la primera que **aún progresan** empiezan con todo nodo válido, y la regla de parejas es la identidad allí. | medido; ninguna progresa |
| **`hStart`** | El estado de arranque del reader (`filterAllAgg kv.2 []`) cumple **`SegExact`** (todo tramo dentro de una **cadena completa**) en las cimas de `OneStep`/`PairHelly`/`RoundExact`; `SegGood` en la cima `TopGoodLadder`. | **ver §4** |
| **`AggInactive`** (`PinDoomed.lean:82`) | El barrido agresivo no quita nada tras el review base. | **demostrado** (`aggInactive_of_revOk`, `PairHelly.lean:205`) |

Detalle de las definiciones que no son obvias:

- **`Seg`** (`OneStep.lean:36` / `TopGoodUp.lean:755`): cadena parcial + miembros poseídos dos a dos.
- **`SegGood`** (`TopGoodUp.lean:543`): todo `Seg` tiene, en **cada paso fuera de él**, una entrada
  común a las tablas de todos sus miembros.
- **`SegExact`** (`SegExact.lean:39`): todo `Seg` se extiende a una `FullChainG` que coincide con él en
  sus pasos.
- **`KeptOwnUp` no incluye "vivo" ni "enlazado"**: que `w` viva en `C` y quede enlazado con el extremo
  lo demuestra aparte `survivesUp_of_keptOwn` (vía `survives_of_pinned_owner` + `link_cleanPair`). Es
  `KeptUp` (el fuerte, `OneStep.lean:895`) el que incorpora el enlace.

Cimas ya escritas (**todas condicionales**, no cerradas), de la más basta a la más fina:

- `TopGoodLadder.readerVerdictW_iff_of_readerSegGood` — hipótesis `ReaderSegGood` (SegGood en todo
  estado del reader; `TopGoodLadder.lean:161,166`).
- `RoundExact.readerVerdictW_iff_of_roundExact` (`RoundExact.lean:34,87`).
- `PairHelly.readerVerdictW_iff_of_pairHelly` (`PairHelly.lean:249`).
- `OneStep.readerVerdictW_iff_of_survives` / `…_of_kept` / `…_of_keptOwn` / `…_of_witPin`
  (`OneStep.lean:808,940,1175,1398`).

Otras cimas viejas, también condicionales: `PinAliveChain.readerVerdictW_iff_of_pinAlive`,
`Ladder2.readerVerdictW_iff_of_triples`, `PinPairs.readerVerdictW_iff_of_pairs`,
`SegExact.readerVerdictW_iff_of_readerSegExact`, `…_of_readerPinnedSegExact`.

## 4. La corrección importante (semilla 11, v190–v191)

**`SegGood`** es **falso en general**. En la fórmula #1 de la semilla 11 (6 variables, 8 cláusulas,
satisfacible, el reader acierta) hay **6 tramos sin cadena** en el primer estado del reader, y el estado
incumple `SegGood`.

En términos de la máquina, el fallo es un **trío muerto hecho de tres parejas vivas**:

- Los tres literales falsos de una cláusula caen en **ventanas distintas**; ningún miembro ve dos a la
  vez.
- En el paso de la cláusula, las tres tablas **se cortan dos a dos pero no las tres juntas**: solo se
  cortarían en la fila `000`, que el mapa no crea.
- Las tablas guardan **parejas**, no tríos; ninguna regla correcta sobre parejas lo borra (cada pareja
  está en una solución real).

Qué se mantiene y qué lo sustituye:

- **`TriExact` cae**: 87 de 26.413 tríos sin cadena común en ese estado (v190 §2). **No llevarla** en la
  inducción.
- **`PairExact` se mantiene**: 0 de 6.742 en ese **mismo** estado (v190 §2).
- **`PrefixSegGood`** (v190/v191, **propuesta, no formalizada**): el reader construye la cadena **desde
  el paso 0**, así que solo pregunta por tramos que empiezan en 0. Medido: de 28.287 tramos en los
  estados del reader de la semilla 11, **18 fallan y 0 de los que fallan empiezan en el paso 0**
  (v190 §4). v191 §4.2 advierte que llevarlo a la inducción tiene un obstáculo de **circularidad**.
- **La pieza que de verdad queda (propuesta B de v191)**: *si una pareja `(x,w)` sobrevive a
  `cleanPair X`, hay una cadena de `X` que pasa por `x`, `w` **y el nodo pinchado** `q`*. Es tres nodos,
  pero con el tercero **fijo** (el pin), no un trío arbitrario.
- `PairExact g → OwnerChained g` es **casi directo** (por autoposesión) pero **aún no está escrito**
  (v191 §8.1).

## 5. Con el mapa binario (v192–v193)

Si cada paso del mapa tiene **≤2 nodos** (bin: `stepCount = 2n+3m+3`, cada cláusula 3 pasos de 2 nodos,
ventana `(0,0,0)` prohibida; v193 §1):

- **Deducido**: `SmallOrHelly` deja de ser hipótesis (hay ≤2 candidatos → `helly_two`); desaparecen las
  cajas, el hueco `000` y `rowBit`.
- **Por medir**: la única hipótesis de tablas de la escalera `OneStep → SegGood/PairHelly` queda en
  **`TriTop`** (`OneStep.lean:257-265,321`): *cada dos miembros del tramo comparten un candidato* (con
  dominio 2: un miembro no puede admitir solo `d=0` y otro solo `d=1`). v192 §4 lo deja explícitamente
  **por comprobar**, no medido.
- **Medido (máquina, no la hipótesis)**: el mapa bin decide igual que el clásico y el exhaustivo en
  **73/73** instancias y con las mismas soluciones (v193 §3). Eso **no** verifica `TriTop`.
- Que la conservación de `PairExact` en el pin tome esa misma forma es **por comprobar** (v192 §6).

## 6. Resumen

| nivel | condición en la máquina | estado |
|---|---|---|
| Solidez | si el reader termina, `φ` es SAT | **demostrado** (solo `WF φ`) |
| Completitud | el reader **nunca se atasca** (`ProgressAgg`) | **abierto** |
| Condición más corta | **`PinAlive`**: pinchar una entrada viva nunca invalida | **abierto** (medido 1.016/1.016, 12.602/12.602) |
| Su significado | **`OwnerChained`**: toda entrada viva de la global está en una cadena | derivado de `PinAlive` |
| Descomposición por pin | `PairExact` + `KeptOwn` + `CleanRest` + `LaterValid` (+ `hStart`) | teoremas condicionales |
| Lo que hay que llevar (v190) | **`PairExact` conservado por el pin**, no `SegGood` ni `TriExact` | medido 0 fallos; **la prueba, pendiente** |
| Prefijos | `PrefixSegGood`: solo los tramos que empiezan en el paso 0 | **medido** (0 fallos); **propuesto**, no formalizado |
| Con el mapa bin | lo único de tablas sería **`TriTop`** | **por medir**; el 73/73 es del mapa, no de esta hipótesis |

En una frase: **el reader funciona si el review nunca deja en la global una entrada sin cadena**; y lo
que queda por demostrar del pin es que una **pareja** que sobrevive a la limpieza sigue teniendo una
cadena que pasa por esa pareja **y por el nodo que se acaba de pinchar**.
